import LastLib.Book04AdelesAndIdeles.Chapter08.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct
open IsDedekindDomain NumberField

/-! ## 8.6 Ordinary and narrow ideal classes -/

abbrev Chapter08RealPlaces (K : Type*) [Field K] [NumberField K] :=
  {w : NumberField.InfinitePlace K // w.IsReal}

abbrev Chapter08SignGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter08RealPlaces K → SignTypeˣ

noncomputable def chapter08RealEmbedding
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter08RealPlaces K) : K →+* ℝ :=
  NumberField.InfinitePlace.embedding_of_isReal w.2

noncomputable def chapter08SignOfUnit
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) (w : Chapter08RealPlaces K) : SignTypeˣ :=
  Units.mk0 (SignType.sign (chapter08RealEmbedding w (a : K))) (by
    sorry)

def chapter08SignHom (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* Chapter08SignGroup K where
  toFun := fun u w => chapter08SignOfUnit (Units.map (algebraMap (Chapter08Integers K) K) u) w
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    funext w
    sorry

def chapter08TotallyPositiveElements (K : Type*) [Field K] [NumberField K] :
    Subgroup Kˣ where
  carrier := {a | ∀ w : Chapter08RealPlaces K,
    0 < chapter08RealEmbedding w (a : K)}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

def chapter08TotallyPositivePrincipalHom (K : Type*) [Field K] [NumberField K] :
    chapter08TotallyPositiveElements K →* Chapter08IdealGroup K :=
  (toPrincipalIdeal (Chapter08Integers K) K).comp
    (chapter08TotallyPositiveElements K).subtype

def chapter08TotallyPositivePrincipalIdeals (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08IdealGroup K) :=
  MonoidHom.range (chapter08TotallyPositivePrincipalHom K)

abbrev Chapter08NarrowClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ chapter08TotallyPositivePrincipalIdeals K

abbrev Chapter08OrdinaryIdealQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ (toPrincipalIdeal (Chapter08Integers K) K).range

def chapter08NarrowToOrdinary (K : Type*) [Field K] [NumberField K] :
    Chapter08NarrowClassGroup K →* Chapter08OrdinaryIdealQuotient K :=
  QuotientGroup.lift (chapter08TotallyPositivePrincipalIdeals K)
    (QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range) (by
      intro x hx
      sorry)

theorem chapter08_narrow_to_ordinary_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToOrdinary K) := by
  sorry

def chapter08NarrowToClassGroup (K : Type*) [Field K] [NumberField K] :
    Chapter08NarrowClassGroup K →* Chapter08OrdinaryClassGroup K :=
  (ClassGroup.equiv K).symm.toMonoidHom.comp (chapter08NarrowToOrdinary K)

theorem chapter08_narrow_to_class_group_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToClassGroup K) := by
  sorry

/-! Weak approximation supplies a field element with any prescribed real sign pattern.  This is
the bridge needed to define the sign-to-narrow-class map. -/

/- Local dependency guess for the later fixup pass: the preceding chapters expose weak
approximation in the form needed to realize every finite real sign pattern by an element of Kˣ. -/

theorem chapter08_sign_pattern_realization
    (K : Type*) [Field K] [NumberField K]
    (s : Chapter08SignGroup K) :
    ∃ a : Kˣ, chapter08SignOfUnit a = s := by
  sorry

noncomputable def chapter08SignRepresentative
    {K : Type*} [Field K] [NumberField K]
    (s : Chapter08SignGroup K) : Kˣ :=
  Classical.choose (chapter08_sign_pattern_realization K s)

theorem chapter08SignRepresentative_sign
    {K : Type*} [Field K] [NumberField K]
    (s : Chapter08SignGroup K) :
    chapter08SignOfUnit (chapter08SignRepresentative s) = s := by
  exact Classical.choose_spec (chapter08_sign_pattern_realization K s)

def chapter08SignToNarrowClass (K : Type*) [Field K] [NumberField K] :
    Chapter08SignGroup K →* Chapter08NarrowClassGroup K where
  toFun := fun s =>
    QuotientGroup.mk' (chapter08TotallyPositivePrincipalIdeals K)
      (toPrincipalIdeal (Chapter08Integers K) K (chapter08SignRepresentative s))
  map_one' := by
    sorry
  map_mul' := by
    intro s t
    sorry

theorem chapter08_sign_narrow_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsExact (chapter08SignHom K) (chapter08SignToNarrowClass K) ∧
      chapter08IsExact (chapter08SignToNarrowClass K) (chapter08NarrowToOrdinary K) ∧
      Function.Surjective (chapter08NarrowToOrdinary K) := by
  sorry

theorem chapter08_narrow_class_group_maps_onto_ordinary
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08NarrowToClassGroup K) :=
  chapter08_narrow_to_class_group_surjective K

theorem chapter08_narrow_equals_ordinary_of_sign_surjective
    (K : Type*) [Field K] [NumberField K]
    (hs : Function.Surjective (chapter08SignHom K)) :
    Function.Bijective (chapter08NarrowToOrdinary K) := by
  sorry

def chapter08RealQuadratic (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 ∧ Nonempty (Chapter08RealPlaces K)

def chapter08UnitNormMinusOne (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ u : (Chapter08Integers K)ˣ, Algebra.norm ℚ (u : K) = -1

theorem chapter08_real_quadratic_norm_minus_one_gives_all_signs
    (K : Type*) [Field K] [NumberField K]
    (hquadratic : chapter08RealQuadratic K)
    (hnorm : chapter08UnitNormMinusOne K) :
    Function.Surjective (chapter08SignHom K) := by
  sorry

def chapter08FullRealSignImage (K : Type*) [Field K] [NumberField K] : Prop :=
  Function.Surjective (chapter08SignHom K)

theorem chapter08_full_sign_image_implies_ordinary_narrow_agree
    (K : Type*) [Field K] [NumberField K]
    (h : chapter08FullRealSignImage K) :
    Function.Bijective (chapter08NarrowToOrdinary K) :=
  chapter08_narrow_equals_ordinary_of_sign_surjective K h

def chapter08PositiveInfiniteIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08InfiniteIdeles K) where
  carrier := {x | ∀ w : Chapter08RealPlaces K,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      (x.1 w.1)}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

def chapter08InfiniteIdeleSignHom (K : Type*) [Field K] [NumberField K] :
    Chapter08InfiniteIdeles K →* Chapter08SignGroup K where
  toFun := fun x w =>
    Units.mk0
      (SignType.sign
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x.1 w.1))) (by
          sorry)
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    funext w
    sorry

theorem chapter08_infinite_idele_sign_kernel
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08InfiniteIdeleSignHom K) =
      chapter08PositiveInfiniteIdeles K := by
  sorry

/-! The complex coordinates have no sign quotient here; their arguments remain continuous data. -/

/-! The connected-component quotient at a real place has two elements and no valuation coordinate. -/

def chapter08PositiveRealUnits : Subgroup ℝˣ where
  carrier := {u | 0 < (u : ℝ)}
  one_mem' := by simp
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

def chapter08RealUnitSignHom : ℝˣ →* SignTypeˣ where
  toFun := fun u => Units.mk0 (SignType.sign (u : ℝ)) (by
    exact (sign_ne_zero).2 u.ne_zero)
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

theorem chapter08_real_unit_sign_surjective :
    Function.Surjective chapter08RealUnitSignHom := by
  sorry

theorem chapter08_real_unit_sign_kernel :
    MonoidHom.ker chapter08RealUnitSignHom = chapter08PositiveRealUnits := by
  sorry

noncomputable def chapter08RealUnitComponentQuotientEquiv :
    (ℝˣ ⧸ chapter08PositiveRealUnits) ≃* SignTypeˣ :=
  QuotientGroup.liftEquiv chapter08PositiveRealUnits
    chapter08_real_unit_sign_surjective (chapter08_real_unit_sign_kernel).symm

theorem chapter08_real_component_quotient_is_sign_group :
    Nonempty ((ℝˣ ⧸ chapter08PositiveRealUnits) ≃* SignTypeˣ) := by
  exact ⟨chapter08RealUnitComponentQuotientEquiv⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter08
