import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.4 Finiteness of ray class groups -/

theorem chapter11_exists_residue_sign_to_ray_class_hom (m : RayModulus K) :
    ∃ f : chapter11RayResidueSignGroup m →* chapter11RayClassGroup m,
      Function.MulExact (chapter11GlobalUnitResidueSignHom m) f ∧
        Function.MulExact f (chapter11RayClassToOrdinaryClassHom m) ∧
          Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  sorry

noncomputable def chapter11ResidueSignToRayClassHom (m : RayModulus K) :
    chapter11RayResidueSignGroup m →* chapter11RayClassGroup m :=
  Classical.choose (chapter11_exists_residue_sign_to_ray_class_hom m)

theorem chapter11_ray_class_residue_sign_exact_sequence (m : RayModulus K) :
    Function.MulExact (chapter11GlobalUnitResidueSignHom m)
        (chapter11ResidueSignToRayClassHom m) ∧
      Function.MulExact (chapter11ResidueSignToRayClassHom m)
        (chapter11RayClassToOrdinaryClassHom m) ∧
      Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  exact Classical.choose_spec (chapter11_exists_residue_sign_to_ray_class_hom m)

/- The first arrow is deliberately only a homomorphism.  Its kernel is the
global-unit congruence subgroup, so no injectivity claim is made. -/

theorem chapter11_ray_residue_group_is_finite (m : RayModulus K) :
    Finite (chapter11RayResidueGroup m) := by
  sorry

theorem chapter11_ray_sign_group_is_finite (m : RayModulus K) :
    Finite (chapter11RaySignGroup m) := by
  infer_instance

theorem chapter11_ray_class_group_is_finite (m : RayModulus K) :
    Finite (chapter11RayClassGroup m) := by
  sorry

noncomputable instance chapter11_ray_class_group_fintype (m : RayModulus K) :
    Fintype (chapter11RayClassGroup m) := by
  letI : Finite (chapter11RayClassGroup m) := chapter11_ray_class_group_is_finite m
  exact Fintype.ofFinite _

theorem chapter11_ray_class_group_is_finite_index_over_ordinary_class_group
    (m : RayModulus K) :
    Finite (chapter11RayResidueSignGroup m) ∧
      Finite (Chapter11OrdinaryClassGroup K) ∧
      Function.Surjective (chapter11RayClassToOrdinaryClassHom m) := by
  sorry

end
