import LastLib.Book06GlobalClassFieldTheory.Chapter07.Section03ConductorsOfExtensionsAndCharacters

/-!
# 7.4. Existence and maximality of ray class fields

The `RayClassField` structure packages the finite abelian extension supplied by
the existence theorem.  Its two equivalences are the book's Galois/ray-class
identification and the finite Galois presentation needed for local subgroup
calculations.  The maximality theorem is stated first as the canonical kernel
factorization; this is the group-theoretic form from which field containment is
obtained by the preceding class-field correspondence.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

universe uL

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
variable {D : IdeleContext K I}
variable {G : Type*} [CommGroup G] [Fintype G]

def rayClassClassQuotient (D : IdeleContext K I) (m : Modulus K) :
    ideleClassGroup D →* rayClassGroup D m :=
  QuotientGroup.mk' (rayClassSubgroup D m)

structure RayClassField (D : IdeleContext K I) (m : Modulus K) where
  canonicalBridge : CanonicalRayClassFieldBridge D m
  L : Type uL
  [fieldL : Field L]
  [numberFieldL : NumberField L]
  [algebraKL : Algebra K L]
  [finiteDimensionalKL : FiniteDimensional K L]
  [isGaloisKL : IsGalois K L]
  [isAbelianGaloisKL : IsAbelianGalois K L]
  G : Type uL
  [commGroupG : CommGroup G]
  [fintypeG : Fintype G]
  galoisEquiv : G ≃* Gal(L / K)
  rayEquiv : rayClassGroup D m ≃* G
  canonicalExtensionData :
    LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06FiniteAbelianExtensionData
      K L
  canonical_norm_subgroup_eq :
    LastLib.Book06GlobalClassFieldTheory.Chapter06.chapter06CanonicalNormSubgroup
      canonicalExtensionData = canonicalBridge.canonicalSubgroup.subgroup
  canonical_artin_commutes :
    galoisEquiv.toMonoidHom.comp
        (rayEquiv.toMonoidHom.comp
          (QuotientGroup.mk' (rayClassSubgroup D m))) =
      (LastLib.Book06GlobalClassFieldTheory.Chapter06.chapter06CanonicalClassArtinGalois
        canonicalExtensionData).comp
        canonicalBridge.canonicalClassGroupEquiv.toMonoidHom

attribute [instance] RayClassField.fieldL RayClassField.algebraKL
  RayClassField.numberFieldL RayClassField.finiteDimensionalKL RayClassField.isGaloisKL
  RayClassField.isAbelianGaloisKL RayClassField.commGroupG RayClassField.fintypeG

def rayClassFieldClassArtin
    (R : RayClassField D m) : ideleClassGroup D →* R.G :=
  R.rayEquiv.toMonoidHom.comp (rayClassClassQuotient D m)

def rayClassFieldKernel (R : RayClassField D m) :
    Subgroup (ideleClassGroup D) := (rayClassFieldClassArtin R).ker

/-! Existence is stated only after the canonical Chapter 6 bridge supplies the
open finite-index quotient and its norm--Artin enrichment. -/

theorem ray_class_field_existence
    (B : CanonicalRayClassFieldBridge D m)
    (hExist :
      LastLib.Book06GlobalClassFieldTheory.Chapter01.EveryOpenFiniteIndexSubgroupIsAClassNorm
        K)
    (enrich :
      ∀ R : LastLib.Book06GlobalClassFieldTheory.Chapter01.ClassFieldNormRealization
          K B.canonicalSubgroup.subgroup,
        letI : Field R.L := R.field_L
        letI : NumberField R.L := R.numberField_L
        letI : Algebra K R.L := R.algebra_K_L
        letI : FiniteDimensional K R.L := R.finiteDimensional_K_L
        letI : IsAbelianGalois K R.L := R.abelianGalois_K_L
        Nonempty
          (LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06FiniteAbelianExtensionEnrichment
            K R.L R.normData)) :
    Nonempty (RayClassField D m) := by
  sorry

theorem ray_class_field_unique
    (R S : RayClassField D m)
    (hbridge : R.canonicalBridge = S.canonicalBridge) :
    Nonempty (R.L ≃ₐ[K] S.L) := by
  sorry

noncomputable def ray_class_field_galois_group_is_ray_class_group
    (R : RayClassField D m) :
    Gal(R.L / K) ≃* rayClassGroup D m := by
  exact R.galoisEquiv.symm.trans R.rayEquiv.symm

theorem ray_class_field_presentations_have_equivalent_galois_groups
    (R S : RayClassField D m) : Nonempty (R.G ≃* S.G) := by
  exact ⟨R.rayEquiv.symm.trans S.rayEquiv⟩

theorem ray_class_field_contains_every_bounded_canonical_extension
    (R : RayClassField D m)
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (E :
      LastLib.Book06GlobalClassFieldTheory.Chapter06.Chapter06FiniteAbelianExtensionData
        K L)
    (h : R.canonicalBridge.canonicalSubgroup.subgroup ≤
      (LastLib.Book06GlobalClassFieldTheory.Chapter06.chapter06CanonicalClassArtinGalois E).ker) :
    Nonempty (L →ₐ[K] R.L) := by
  sorry

theorem ray_class_field_kernel_eq_ray_class_subgroup
    (R : RayClassField D m) :
    rayClassFieldKernel R = rayClassSubgroup D m := by
  sorry

theorem ray_class_field_kernel_is_open_and_finite_index
    (R : RayClassField D m) :
    IsOpen (rayClassFieldKernel R : Set (ideleClassGroup D)) ∧
      (rayClassFieldKernel R).FiniteIndex := by
  rw [ray_class_field_kernel_eq_ray_class_subgroup R]
  exact ⟨rayClassSubgroup_isOpen D m, by sorry⟩

/-! ### Maximality and the class-field correspondence -/

def ArtinPresentationFactorsThroughRayClassField
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G) : Prop :=
  ∃ q : R.G →* G,
    A.classArtin = q.comp (rayClassFieldClassArtin R)

/-! Downstream chapters use the field-containment terminology for the same
presentation-level factorization.  Keep the name as an explicit alias; the
canonical field-containment theorem above is available when an actual
Chapter 6 extension package is supplied. -/

abbrev ArtinPresentationIsSubextension
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G) : Prop :=
  ArtinPresentationFactorsThroughRayClassField R A

theorem ray_class_field_contains_every_bounded_artin_presentation
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ExtensionConductorBound A m) :
    ArtinPresentationFactorsThroughRayClassField R A := by
  sorry

theorem ray_class_field_maximality_kernel_form
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ExtensionConductorBound A m) :
    rayClassSubgroup D m ≤ artinKernel A := by
  exact ray_units_are_killed_by_an_extension_conductor_bound A m h

theorem ray_class_field_norm_subgroup_inclusion
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ExtensionConductorBound A m) :
    rayClassFieldKernel R ≤ artinKernel A := by
  rw [ray_class_field_kernel_eq_ray_class_subgroup R]
  exact ray_class_field_maximality_kernel_form A h

theorem bounded_artin_presentations_factor_through_the_ray_class_field
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
  (h : extensionConductor A ≤ m) :
    ArtinPresentationFactorsThroughRayClassField R A := by
  exact ray_class_field_contains_every_bounded_artin_presentation R A
    ((extensionConductor_is_least_modulus A m).mp h)

theorem ray_class_field_factorizations_have_conductor_dividing_the_modulus
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ArtinPresentationFactorsThroughRayClassField R A) :
    extensionConductor A ≤ m := by
  sorry

theorem ray_class_field_is_maximal_for_bounded_artin_presentations
    (R : RayClassField D m) :
    ∀ A : AbelianArtinData (K := K) (I := I) D G,
      extensionConductor A ≤ m → ArtinPresentationFactorsThroughRayClassField R A := by
  intro A h
  exact bounded_artin_presentations_factor_through_the_ray_class_field R A h

/-! ### Local decomposition, inertia, and upper ramification interfaces -/

def rayClassFieldLocalArtin
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* R.G :=
  R.rayEquiv.toMonoidHom.comp
    ((rayClassClassQuotient D m).comp
      ((ideleClassQuotient D).comp (D.finiteComponent v)))

def rayClassFieldLocalArtinGalois
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* Gal(R.L / K) :=
  R.galoisEquiv.toMonoidHom.comp (rayClassFieldLocalArtin R v)

def rayClassFieldInfiniteLocalArtin
    (R : RayClassField D m) (v : NumberField.InfinitePlace K) :
    v.Completionˣ →* R.G :=
  R.rayEquiv.toMonoidHom.comp
    ((rayClassClassQuotient D m).comp
      ((ideleClassQuotient D).comp (D.infiniteComponent v)))

def rayClassFieldInfiniteLocalArtinGalois
    (R : RayClassField D m) (v : NumberField.InfinitePlace K) :
    v.Completionˣ →* Gal(R.L / K) :=
  R.galoisEquiv.toMonoidHom.comp (rayClassFieldInfiniteLocalArtin R v)

def finiteDecompositionSubgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) : Subgroup R.G :=
  Subgroup.map (rayClassFieldLocalArtin R v) ⊤

def finiteInertiaSubgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) : Subgroup R.G :=
  Subgroup.map (rayClassFieldLocalArtin R v)
    (finiteUnitFiltration v 0)

def finiteUpperRamificationSubgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) (r : ℕ) : Subgroup R.G :=
  Subgroup.map (rayClassFieldLocalArtin R v) (finiteUnitFiltration v r)

def infiniteDecompositionSubgroup
    (R : RayClassField D m) (v : NumberField.InfinitePlace K) : Subgroup R.G :=
  Subgroup.map (rayClassFieldInfiniteLocalArtin R v) ⊤

theorem finite_local_image_is_decomposition_subgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    finiteDecompositionSubgroup R v =
      Subgroup.map (rayClassFieldLocalArtin R v) ⊤ := rfl

theorem finite_unit_image_is_inertia_subgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    finiteInertiaSubgroup R v =
      Subgroup.map (rayClassFieldLocalArtin R v) (finiteUnitFiltration v 0) := rfl

theorem finite_upper_image_is_upper_ramification_subgroup
    (R : RayClassField D m) (v : NumberField.FinitePlace K) (r : ℕ) :
    finiteUpperRamificationSubgroup R v r =
      Subgroup.map (rayClassFieldLocalArtin R v) (finiteUnitFiltration v r) := rfl

theorem finite_place_outside_modulus_has_trivial_inertia
    (R : RayClassField D m) (v : NumberField.FinitePlace K)
    (hv : ¬v.maximalIdeal.asIdeal ∣ m.finitePart) :
    finiteInertiaSubgroup R v = ⊥ := by
  sorry

theorem prescribed_depth_is_killed_in_the_ray_class_field
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    finiteUnitFiltration v (m.finiteExponent v) ≤
      (rayClassFieldLocalArtin R v).ker := by
  sorry

theorem real_place_not_in_modulus_has_trivial_infinite_image
    (R : RayClassField D m) (v : NumberField.InfinitePlace K)
    (hv : ¬v.IsReal ∨ (∀ h : v.IsReal,
      (⟨v, h⟩ : RealPlace K) ∉ m.infinitePart)) :
    infiniteDecompositionSubgroup R v = ⊥ := by
  sorry

theorem selected_real_place_kills_the_positive_local_subgroup
    (R : RayClassField D m) (v : RealPlace K) :
    v ∈ m.infinitePart →
      ∀ x : v.1.Completionˣ,
        x ∈ realPositiveUnitSubgroup v →
          rayClassFieldInfiniteLocalArtin R v.1 x = 1 := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
