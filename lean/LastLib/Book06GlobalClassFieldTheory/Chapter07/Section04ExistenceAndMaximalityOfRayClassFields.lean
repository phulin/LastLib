import LastLib.Book06GlobalClassFieldTheory.Chapter07.Dependencies
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
  L : Type uL
  [fieldL : Field L]
  [algebraKL : Algebra K L]
  [finiteDimensionalKL : FiniteDimensional K L]
  [isGaloisKL : IsGalois K L]
  G : Type uL
  [commGroupG : CommGroup G]
  [fintypeG : Fintype G]
  galoisEquiv : G ≃* Gal(L / K)
  rayEquiv : rayClassGroup D m ≃* G

attribute [instance] RayClassField.fieldL RayClassField.algebraKL
  RayClassField.finiteDimensionalKL RayClassField.isGaloisKL
  RayClassField.commGroupG RayClassField.fintypeG

def rayClassFieldClassArtin
    (R : RayClassField D m) : ideleClassGroup D →* R.G :=
  R.rayEquiv.toMonoidHom.comp (rayClassClassQuotient D m)

def rayClassFieldKernel (R : RayClassField D m) :
    Subgroup (ideleClassGroup D) := (rayClassFieldClassArtin R).ker

theorem ray_class_field_existence_theorem
    (D : IdeleContext K I) (m : Modulus K) :
    Nonempty (RayClassField D m) := by
  /- LOCAL_DEPENDENCY_GUESS: replace this interface proof by the preceding
     existence theorem for open finite-index idele-class subgroups. -/
  sorry

noncomputable def ray_class_field_galois_group_is_ray_class_group
    (R : RayClassField D m) :
    Gal(R.L / K) ≃* rayClassGroup D m := by
  exact R.galoisEquiv.symm.trans R.rayEquiv.symm

theorem ray_class_field_is_unique_up_to_K_equivalence
    (R S : RayClassField D m) : Nonempty (R.L ≃ₐ[K] S.L) := by
  sorry

theorem ray_class_field_kernel_eq_ray_class_subgroup
    (R : RayClassField D m) :
    rayClassFieldKernel R = rayClassSubgroup D m := by
  sorry

theorem ray_class_field_kernel_is_open_and_finite_index
    (R : RayClassField D m) :
    IsOpen (rayClassFieldKernel R : Set (ideleClassGroup D)) ∧
      Finite (rayClassGroup D m) := by
  rw [ray_class_field_kernel_eq_ray_class_subgroup R]
  exact ⟨rayClassSubgroup_isOpen D m, rayClassGroup_finite D m⟩

/-! ### Maximality and the class-field correspondence -/

def ArtinPresentationIsSubextension
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G) : Prop :=
  ∃ q : R.G →* G,
    A.classArtin = q.comp (rayClassFieldClassArtin R)

theorem ray_class_field_contains_every_bounded_artin_presentation
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ExtensionConductorBound A m) :
    ArtinPresentationIsSubextension R A := by
  sorry

theorem ray_class_field_maximality_kernel_form
    (_R : RayClassField D m)
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
  exact ray_class_field_maximality_kernel_form R A h

theorem bounded_extensions_are_subextensions_of_the_ray_class_field
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
  (h : extensionConductor A ≤ m) :
    ArtinPresentationIsSubextension R A := by
  exact ray_class_field_contains_every_bounded_artin_presentation R A
    ((extensionConductor_is_least_modulus A m).mp h)

theorem ray_class_field_subextensions_have_conductor_dividing_the_modulus
    (R : RayClassField D m)
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ArtinPresentationIsSubextension R A) :
    extensionConductor A ≤ m := by
  sorry

theorem ray_class_field_is_the_maximal_abelian_extension_of_modulus
    (R : RayClassField D m) :
    ∀ A : AbelianArtinData (K := K) (I := I) D G,
      extensionConductor A ≤ m → ArtinPresentationIsSubextension R A := by
  intro A h
  exact bounded_extensions_are_subextensions_of_the_ray_class_field R A h

/-! ### Local decomposition, inertia, and upper ramification interfaces -/

def rayClassFieldLocalArtin
    (R : RayClassField D m) (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* R.G :=
  R.rayEquiv.toMonoidHom.comp
    ((rayClassClassQuotient D m).comp
      ((ideleClassQuotient D).comp (D.finiteComponent v)))

def rayClassFieldInfiniteLocalArtin
    (R : RayClassField D m) (v : NumberField.InfinitePlace K) :
    v.Completionˣ →* R.G :=
  R.rayEquiv.toMonoidHom.comp
    ((rayClassClassQuotient D m).comp
      ((ideleClassQuotient D).comp (D.infiniteComponent v)))

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
