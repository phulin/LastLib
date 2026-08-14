import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section03PrincipalDivisorsAndLinearEquivalence
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/-! ## 4.4. The divisor--Picard correspondence -/

/-! ### Isomorphism classes of line bundles -/

instance chapter04LineBundleSetoid (X : Scheme.{u}) :
    Setoid (Chapter04LineBundle X) where
  r := chapter04LineBundleIsomorphic
  iseqv :=
    { refl := chapter04_lineBundleIsomorphic_refl
      symm := chapter04_lineBundleIsomorphic_symm
      trans := chapter04_lineBundleIsomorphic_trans }

abbrev Chapter04PicardGroup (X : Scheme.{u}) :=
  Quotient (chapter04LineBundleSetoid X)

noncomputable def chapter04LineBundleClass {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : Chapter04PicardGroup X :=
  Quotient.mk' L

theorem chapter04_lineBundleClass_eq_iff {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) :
    chapter04LineBundleClass L = chapter04LineBundleClass M ↔
      chapter04LineBundleIsomorphic L M := by
  sorry

noncomputable def chapter04PicardTensor {X : Scheme.{u}}
    (a b : Chapter04PicardGroup X) : Chapter04PicardGroup X :=
  Quotient.liftOn₂ a b
    (fun L M => chapter04LineBundleClass (chapter04LineBundleTensor L M))
    (by
      intro L₁ M₁ L₂ M₂ hL hM
      apply Quotient.sound
      sorry)

noncomputable def chapter04PicardOne (X : Scheme.{u}) : Chapter04PicardGroup X :=
  chapter04LineBundleClass (chapter04TrivialLineBundle X)

noncomputable def chapter04PicardInverse {X : Scheme.{u}}
    (a : Chapter04PicardGroup X) : Chapter04PicardGroup X :=
  Quotient.liftOn a
    (fun L => chapter04LineBundleClass (chapter04DualLineBundle L))
    (by
      intro L M hLM
      apply Quotient.sound
      sorry)

theorem chapter04_picardTensor_assoc {X : Scheme.{u}}
    (a b c : Chapter04PicardGroup X) :
    chapter04PicardTensor (chapter04PicardTensor a b) c =
      chapter04PicardTensor a (chapter04PicardTensor b c) := by
  sorry

theorem chapter04_picardOne_tensor {X : Scheme.{u}}
    (a : Chapter04PicardGroup X) :
    chapter04PicardTensor (chapter04PicardOne X) a = a := by
  sorry

theorem chapter04_picard_tensor_one {X : Scheme.{u}}
    (a : Chapter04PicardGroup X) :
    chapter04PicardTensor a (chapter04PicardOne X) = a := by
  sorry

theorem chapter04_picardTensor_comm {X : Scheme.{u}}
    (a b : Chapter04PicardGroup X) :
    chapter04PicardTensor a b = chapter04PicardTensor b a := by
  sorry

theorem chapter04_picard_inverse_tensor {X : Scheme.{u}}
    (a : Chapter04PicardGroup X) :
    chapter04PicardTensor (chapter04PicardInverse a) a =
      chapter04PicardOne X := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf Picard imports do not package the
quotient-level group structure, so it is assembled from the tensor operations
and the laws proved above. -/
noncomputable instance chapter04PicardGroupCommGroup (X : Scheme.{u}) :
    CommGroup (Chapter04PicardGroup X) where
  mul := chapter04PicardTensor
  one := chapter04PicardOne X
  inv := chapter04PicardInverse
  mul_assoc := chapter04_picardTensor_assoc
  one_mul := chapter04_picardOne_tensor
  mul_one := chapter04_picard_tensor_one
  inv_mul_cancel := chapter04_picard_inverse_tensor
  mul_comm := chapter04_picardTensor_comm

theorem chapter04_picardGroupCommGroup_exists (X : Scheme.{u}) :
    Nonempty (CommGroup (Chapter04PicardGroup X)) := by
  exact ⟨chapter04PicardGroupCommGroup X⟩

theorem chapter04_picardClass_tensor {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) :
    chapter04PicardTensor (chapter04LineBundleClass L)
      (chapter04LineBundleClass M) =
      chapter04LineBundleClass (chapter04LineBundleTensor L M) := by
  rfl

theorem chapter04_picardClass_one {X : Scheme.{u}} :
    chapter04PicardOne X = chapter04LineBundleClass (chapter04TrivialLineBundle X) := by
  rfl

/-! ### The map from divisor classes to Picard classes -/

instance chapter04CartierDivisorSetoid {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    Setoid (Chapter04CartierDivisor X) where
  r := chapter04CartierDivisorsLinearlyEquivalent
  iseqv :=
    { refl := chapter04_cartier_linearEquivalence_refl
      symm := chapter04_cartier_linearEquivalence_symm
      trans := chapter04_cartier_linearEquivalence_trans }

abbrev Chapter04CartierDivisorClass {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :=
  Quotient (chapter04CartierDivisorSetoid (X := X))

noncomputable def chapter04CartierDivisorClassMk {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04CartierDivisorClass (X := X) :=
  Quotient.mk' D

/-! The quotient of Cartier divisors is a commutative group: multiplication
   below is induced by addition of local equations. -/
noncomputable def chapter04CartierDivisorClassMul {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a b : Chapter04CartierDivisorClass (X := X)) :
    Chapter04CartierDivisorClass (X := X) :=
  Quotient.liftOn₂ a b
    (fun D E => chapter04CartierDivisorClassMk
      (chapter04CartierDivisorAdd D E))
    (by
      intro D₁ E₁ D₂ E₂ hD hE
      apply Quotient.sound
      sorry)

noncomputable def chapter04CartierDivisorClassOne (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    Chapter04CartierDivisorClass (X := X) :=
  chapter04CartierDivisorClassMk (chapter04CartierDivisorZero (X := X))

noncomputable def chapter04CartierDivisorClassInv {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a : Chapter04CartierDivisorClass (X := X)) :
    Chapter04CartierDivisorClass (X := X) :=
  Quotient.liftOn a
    (fun D => chapter04CartierDivisorClassMk
      (chapter04CartierDivisorNeg D))
    (by
      intro D E hDE
      apply Quotient.sound
      sorry)

theorem chapter04_cartierDivisorClass_mul_assoc {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a b c : Chapter04CartierDivisorClass (X := X)) :
    chapter04CartierDivisorClassMul (chapter04CartierDivisorClassMul a b) c =
      chapter04CartierDivisorClassMul a (chapter04CartierDivisorClassMul b c) := by
  sorry

theorem chapter04_cartierDivisorClass_one_mul {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a : Chapter04CartierDivisorClass (X := X)) :
    chapter04CartierDivisorClassMul (chapter04CartierDivisorClassOne X) a = a := by
  sorry

theorem chapter04_cartierDivisorClass_mul_one {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a : Chapter04CartierDivisorClass (X := X)) :
    chapter04CartierDivisorClassMul a (chapter04CartierDivisorClassOne X) = a := by
  sorry

theorem chapter04_cartierDivisorClass_mul_comm {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a b : Chapter04CartierDivisorClass (X := X)) :
    chapter04CartierDivisorClassMul a b =
      chapter04CartierDivisorClassMul b a := by
  sorry

theorem chapter04_cartierDivisorClass_inv_mul_cancel {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (a : Chapter04CartierDivisorClass (X := X)) :
    chapter04CartierDivisorClassMul (chapter04CartierDivisorClassInv a) a =
      chapter04CartierDivisorClassOne X := by
  sorry

noncomputable instance chapter04CartierDivisorClassCommGroup (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    CommGroup (Chapter04CartierDivisorClass (X := X)) where
  mul := chapter04CartierDivisorClassMul
  one := chapter04CartierDivisorClassOne X
  inv := chapter04CartierDivisorClassInv
  mul_assoc := chapter04_cartierDivisorClass_mul_assoc
  one_mul := chapter04_cartierDivisorClass_one_mul
  mul_one := chapter04_cartierDivisorClass_mul_one
  inv_mul_cancel := chapter04_cartierDivisorClass_inv_mul_cancel
  mul_comm := chapter04_cartierDivisorClass_mul_comm

noncomputable def chapter04CartierDivisorToPicardClass {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04PicardGroup X :=
  chapter04LineBundleClass (chapter04OofD D)

theorem chapter04_cartierLinearEquivalence_respected_by_PicardClass
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    {D E : Chapter04CartierDivisor X}
    (h : chapter04CartierDivisorsLinearlyEquivalent D E) :
    chapter04CartierDivisorToPicardClass D =
      chapter04CartierDivisorToPicardClass E := by
  change chapter04LineBundleClass (chapter04OofD D) =
    chapter04LineBundleClass (chapter04OofD E)
  apply (chapter04_lineBundleClass_eq_iff
    (chapter04OofD D) (chapter04OofD E)).2
  exact (chapter04_cartier_linearEquivalence_iff_lineBundle_isomorphic D E).1 h

noncomputable def chapter04DivisorPicardCorrespondence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    Chapter04CartierDivisorClass (X := X) → Chapter04PicardGroup X :=
  Quotient.lift chapter04CartierDivisorToPicardClass
    (by
      intro D E hDE
      apply Quotient.sound
      exact (chapter04_cartier_linearEquivalence_iff_lineBundle_isomorphic D E).1 hDE)

noncomputable def chapter04DivisorPicardCorrespondenceMonoidHom
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    Chapter04CartierDivisorClass (X := X) →* Chapter04PicardGroup X :=
  { toFun := chapter04DivisorPicardCorrespondence
    map_one' := by sorry
    map_mul' := by sorry }

theorem chapter04_divisorPicardCorrespondence_is_monoidHom
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    (chapter04DivisorPicardCorrespondenceMonoidHom (X := X)).toFun =
      chapter04DivisorPicardCorrespondence (X := X) := by
  rfl

theorem chapter04_divisorPicardCorrespondence_on_representative
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D : Chapter04CartierDivisor X) :
    chapter04DivisorPicardCorrespondence (chapter04CartierDivisorClassMk D) =
      chapter04LineBundleClass (chapter04OofD D) := by
  rfl

def chapter04EveryLineBundleHasRationalSection {X : Scheme.{u}}
    [IsIntegral X] : Prop :=
  ∀ L : Chapter04LineBundle X, Nonempty (Chapter04RationalSection L)

def chapter04EveryLineBundleHasAssociatedPointGeneratingRationalSection
    {X : Scheme.{u}} [IsIntegral X] [Chapter04AssociatedPointAPI X] : Prop :=
  ∀ L : Chapter04LineBundle X, ∃ s : Chapter04RationalSection L,
    ∀ x : X, Chapter04AssociatedPointAPI.isAssociated x →
      x = genericPoint X ∧ s.value ≠ 0

theorem chapter04_integral_noetherian_lineBundles_have_rational_sections
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] :
    chapter04EveryLineBundleHasRationalSection (X := X) := by
  sorry

theorem chapter04_integral_noetherian_associated_point_generators
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04AssociatedPointAPI X] :
    chapter04EveryLineBundleHasAssociatedPointGeneratingRationalSection
      (X := X) := by
  sorry

theorem chapter04_associated_point_generators_imply_rational_sections
    {X : Scheme.{u}} [IsIntegral X] [Chapter04AssociatedPointAPI X]
    (h : chapter04EveryLineBundleHasAssociatedPointGeneratingRationalSection
      (X := X)) :
    chapter04EveryLineBundleHasRationalSection (X := X) := by
  intro L
  rcases h L with ⟨s, hs⟩
  exact ⟨s⟩

noncomputable def chapter04ChosenRationalSection {X : Scheme.{u}}
    [IsIntegral X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X))
    (L : Chapter04LineBundle X) : Chapter04RationalSection L :=
  Classical.choice (h L)

noncomputable def chapter04PicardToDivisorClass {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X)) :
    Chapter04PicardGroup X → Chapter04CartierDivisorClass (X := X) :=
  Quotient.lift
    (fun L => chapter04CartierDivisorClassMk
      (chapter04DivisorOfRationalSection L (chapter04ChosenRationalSection h L)))
    (by
      intro L M hLM
      apply Quotient.sound
      sorry)

noncomputable def chapter04DivisorPicardCorrespondenceEquiv
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X)) :
    Chapter04CartierDivisorClass (X := X) ≃ Chapter04PicardGroup X where
  toFun := chapter04DivisorPicardCorrespondence
  invFun := chapter04PicardToDivisorClass h
  left_inv := by
    intro D
    sorry
  right_inv := by
    intro L
    sorry

theorem chapter04_divisorPicardCorrespondence_is_bijective
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X)) :
    Function.Bijective
      (chapter04DivisorPicardCorrespondence (X := X)) := by
  exact (chapter04DivisorPicardCorrespondenceEquiv h).bijective

noncomputable def chapter04DivisorPicardCorrespondenceGroupEquiv
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X)) :
    Chapter04CartierDivisorClass (X := X) ≃* Chapter04PicardGroup X where
  toFun := chapter04DivisorPicardCorrespondence
  invFun := chapter04PicardToDivisorClass h
  left_inv := by
    sorry
  right_inv := by
    sorry
  map_mul' := by
    sorry

theorem chapter04_divisorPicardCorrespondence_is_groupEquiv
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (h : chapter04EveryLineBundleHasRationalSection (X := X)) :
    Nonempty (Chapter04CartierDivisorClass (X := X) ≃*
      Chapter04PicardGroup X) := by
  exact ⟨chapter04DivisorPicardCorrespondenceGroupEquiv h⟩

theorem chapter04_regular_integral_curve_picard_is_divisor_class
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X] :
    Nonempty (Chapter04CartierDivisorClass (X := X) ≃ Chapter04PicardGroup X) := by
  exact ⟨chapter04DivisorPicardCorrespondenceEquiv
    (chapter04_integral_noetherian_lineBundles_have_rational_sections (X := X))⟩

theorem chapter04_divisorPicardCorrespondence_of_associated_point_generators
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04AssociatedPointAPI X]
    (h : chapter04EveryLineBundleHasAssociatedPointGeneratingRationalSection
      (X := X)) :
    Nonempty (Chapter04CartierDivisorClass (X := X) ≃ Chapter04PicardGroup X) := by
  exact ⟨chapter04DivisorPicardCorrespondenceEquiv
    (chapter04_associated_point_generators_imply_rational_sections h)⟩

/- LOCAL_DEPENDENCY_GUESS: `Chapter04CartierDivisor` and the Weil-divisor
   interface in Chapter 3 are deliberately separate presentations.  Local
   factoriality alone cannot prove that their quotient classes agree until
   the canonical order comparison and its bijectivity are supplied. -/
noncomputable def chapter04CartierDivisorClassToWeilDivisorClass
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (hprincipal : ∀ f : X.functionFieldˣ,
      ∀ x : Chapter04CodimensionOnePoint X,
        chapter04CartierOrder (chapter04PrincipalCartierDivisor f) x =
          Chapter04CartierOrderAPI.principalOrder f x) :
    Chapter04CartierDivisorClass (X := X) →
      Chapter04WeilDivisorClass (X := X) :=
  Quotient.lift
    (fun D => chapter04WeilDivisorClassMk (chapter04WeilDivisorOfCartierDivisor D))
    (by
      intro D E hDE
      apply Quotient.sound
      exact (chapter04_cartier_linearEquivalence_to_weil_linearEquivalence
        hprincipal hDE))

class Chapter04CartierWeilClassComparison {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] where
  principal_order :
    ∀ f : X.functionFieldˣ,
      ∀ x : Chapter04CodimensionOnePoint X,
        chapter04CartierOrder (chapter04PrincipalCartierDivisor f) x =
          Chapter04CartierOrderAPI.principalOrder f x
  quotient_bijective :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03LocallyFactorial X →
      Function.Bijective
        (chapter04CartierDivisorClassToWeilDivisorClass
          (X := X) principal_order)

theorem chapter04_cartierWeilClassComparison_exists_of_regular_integral_curve
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03IntegralNoetherianCurve X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular X] :
    Nonempty (Chapter04CartierWeilClassComparison (X := X)) := by
  sorry

theorem chapter04_regular_integral_curve_picard_is_weil_divisor_class
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03IntegralNoetherianCurve X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular X] :
    Nonempty (Chapter04WeilDivisorClass (X := X) ≃ Chapter04PicardGroup X) := by
  sorry

/-! ### Relative Picard classes and base change -/

def chapter04RelativePicardEquivalent {X S : Scheme.{u}}
    (f : X ⟶ S) (L M : Chapter04LineBundle X) : Prop :=
  ∃ N : Chapter04LineBundle S,
    chapter04LineBundleIsomorphic
      (chapter04LineBundleTensor L (chapter04PullbackLineBundle f N)) M

theorem chapter04_pullback_from_base_does_not_change_fiber_class
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (N : Chapter04LineBundle S) :
    chapter04RelativePicardEquivalent f L
      (chapter04LineBundleTensor L (chapter04PullbackLineBundle f N)) := by
  exact ⟨N, chapter04_lineBundleIsomorphic_refl _⟩

theorem chapter04_relative_equivalence_is_fiberwise
    {X S : Scheme.{u}} (f : X ⟶ S) (L M : Chapter04LineBundle X)
    (h : chapter04RelativePicardEquivalent f L M) :
    chapter04FiberwiseLineBundleEquivalent f L M := by
  sorry

/-! Cartier pullback is recorded together with its line-bundle compatibility;
the latter is the precise bridge used by the relative Picard construction. -/
structure Chapter04CartierPullbackData {X Y : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [Chapter04TotalQuotientRingAPI Y]
    (g : Y ⟶ X) [Flat g] (D : Chapter04CartierDivisor X) where
  pullback : Chapter04CartierDivisor Y
  lineBundle_pullback_iso :
    chapter04LineBundleIsomorphic (chapter04OofD pullback)
      (chapter04PullbackLineBundle g (chapter04OofD D))

theorem chapter04_cartierPullback_exists {X Y : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [Chapter04TotalQuotientRingAPI Y]
    (g : Y ⟶ X) [Flat g] (D : Chapter04CartierDivisor X) :
    Nonempty (Chapter04CartierPullbackData g D) := by
  sorry

noncomputable def chapter04CartierPullback {X Y : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [Chapter04TotalQuotientRingAPI Y]
    (g : Y ⟶ X) [Flat g] (D : Chapter04CartierDivisor X) :
    Chapter04CartierDivisor Y :=
  (Classical.choice (chapter04_cartierPullback_exists g D)).pullback

def chapter04FurtherBaseChangeMap {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) :
    pullback f (h ≫ g) ⟶ pullback f g :=
  pullback.lift
    (pullback.fst f (h ≫ g))
    (pullback.snd f (h ≫ g) ≫ h)
    (by sorry)

noncomputable def chapter04CartierDivisorOnBaseChange
    {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S)
    [Chapter04TotalQuotientRingAPI X]
    [Chapter04TotalQuotientRingAPI (pullback f g)]
    [Flat g]
    (D : Chapter04CartierDivisor X) :
    Chapter04CartierDivisor (pullback f g) :=
  chapter04CartierPullback (pullback.fst f g) D

theorem chapter04_cartier_baseChange_compatible_with_further_baseChange
    {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    [Chapter04TotalQuotientRingAPI X]
    [Chapter04TotalQuotientRingAPI (pullback f g)]
    [Chapter04TotalQuotientRingAPI (pullback f (h ≫ g))]
    [Flat g] [Flat h] [Flat (chapter04FurtherBaseChangeMap f g h)]
    (D : Chapter04CartierDivisor X) :
    chapter04LineBundleIsomorphic
      (chapter04OofD (chapter04CartierPullback
        (chapter04FurtherBaseChangeMap f g h)
        (chapter04CartierDivisorOnBaseChange f g D)))
      (chapter04OofD (chapter04CartierDivisorOnBaseChange f (h ≫ g) D)) := by
  sorry

theorem chapter04_lineBundle_baseChange_compatible_with_further_baseChange
    {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) (L : Chapter04LineBundle X) :
    chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle
        (chapter04FurtherBaseChangeMap f g h)
        (chapter04PullbackLineBundle (pullback.fst f g) L))
      (chapter04PullbackLineBundle (pullback.fst f (h ≫ g)) L) := by
  sorry

def chapter04RelativePicardBaseChangeClass {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (L : Chapter04LineBundle X) :
    Chapter04PicardGroup (pullback f g) :=
  chapter04LineBundleClass
    (chapter04PullbackLineBundle (pullback.fst f g) L)

theorem chapter04_relativePicard_baseChange_class_compatible
    {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) (L : Chapter04LineBundle X) :
    chapter04RelativePicardBaseChangeClass
        (f := f) (g := h ≫ g) L =
      chapter04LineBundleClass
        (chapter04PullbackLineBundle (chapter04FurtherBaseChangeMap f g h)
          (chapter04PullbackLineBundle (pullback.fst f g) L)) := by
  sorry

/-!
The relative quotient in this chapter is deliberately formulated by the
fiberwise relation above.  No representability of a relative Picard functor
is used: all divisor and line-bundle constructions are made after each base
change, and the two functoriality theorems record compatibility with a second
base change.
-/
def chapter04RelativePicardRelation {X S : Scheme.{u}}
    (f : X ⟶ S) (L M : Chapter04LineBundle X) : Prop :=
  chapter04FiberwiseLineBundleEquivalent f L M

theorem chapter04_relativePicardRelation_refl {X S : Scheme.{u}}
    (f : X ⟶ S) (L : Chapter04LineBundle X) :
    chapter04RelativePicardRelation f L L := by
  sorry

theorem chapter04_relativePicardRelation_symm {X S : Scheme.{u}}
    (f : X ⟶ S) {L M : Chapter04LineBundle X}
    (h : chapter04RelativePicardRelation f L M) :
    chapter04RelativePicardRelation f M L := by
  sorry

theorem chapter04_relativePicardRelation_trans {X S : Scheme.{u}}
    (f : X ⟶ S) {L M N : Chapter04LineBundle X}
    (hLM : chapter04RelativePicardRelation f L M)
    (hMN : chapter04RelativePicardRelation f M N) :
    chapter04RelativePicardRelation f L N := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
