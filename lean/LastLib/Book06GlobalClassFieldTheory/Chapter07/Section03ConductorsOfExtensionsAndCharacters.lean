import LastLib.Book06GlobalClassFieldTheory.Chapter07.Dependencies

/-!
# 7.3. Conductors of extensions and characters

The definitions in this file separate the finite local norm condition from the
global Artin presentation.  This makes the conductor bounds usable both for a
finite abelian extension and for a finite-order idele class character.
-/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter07

open scoped BigOperators nonZeroDivisors
open NumberField

noncomputable section

variable {K I : Type*} [Field K] [NumberField K]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
variable {D : IdeleContext K I}
variable {G : Type*} [CommGroup G] [Fintype G]

/-! ### Extension conductors -/

def extensionConductorExponent (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) : ℕ :=
  sInf {n : ℕ | finiteUnitFiltration v n ≤ A.finiteLocalNorm v}

def extensionLocalArtin
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* G :=
  A.artin.comp (D.finiteComponent v)

theorem extensionLocalNorm_eq_localArtin_kernel
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    A.finiteLocalNorm v = (extensionLocalArtin A v).ker := by
  exact A.finiteLocalNorm_eq_localArtin_kernel v

theorem extensionConductorExponent_mem
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    finiteUnitFiltration v (extensionConductorExponent A v) ≤ A.finiteLocalNorm v := by
  sorry

theorem extensionConductorExponent_is_least
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) (n : ℕ)
    (hn : finiteUnitFiltration v n ≤ A.finiteLocalNorm v) :
    extensionConductorExponent A v ≤ n := by
  sorry

noncomputable def extensionConductorIdeal
    (A : AbelianArtinData (K := K) (I := I) D G) : Ideal (𝓞 K) :=
  ∏ᶠ v : NumberField.FinitePlace K,
    v.maximalIdeal.asIdeal ^ extensionConductorExponent A v

def extensionConductorFiniteSupport
    (A : AbelianArtinData (K := K) (I := I) D G) : Set (NumberField.FinitePlace K) :=
  {v | extensionConductorExponent A v ≠ 0}

theorem extensionConductorFiniteSupport_finite
    (A : AbelianArtinData (K := K) (I := I) D G) :
    (extensionConductorFiniteSupport A).Finite := by
  sorry

theorem extensionConductorIdeal_ne_bot
    (A : AbelianArtinData (K := K) (I := I) D G) :
    extensionConductorIdeal A ≠ ⊥ := by
  sorry

noncomputable def extensionConductor
    (A : AbelianArtinData (K := K) (I := I) D G) : Modulus K := by
  classical
  exact
    { finitePart := extensionConductorIdeal A
      finitePart_ne_bot := extensionConductorIdeal_ne_bot A
      infinitePart := Finset.univ.filter A.complexified }

@[simp] theorem extensionConductor_finitePart
    (A : AbelianArtinData (K := K) (I := I) D G) :
    (extensionConductor A).finitePart = extensionConductorIdeal A := rfl

theorem extensionConductor_realPart_iff
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : RealPlace K) :
    v ∈ (extensionConductor A).infinitePart ↔ A.complexified v := by
  simp [extensionConductor]

def FinitePlaceUnramifiedAt
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) : Prop :=
  finiteUnitFiltration v 0 ≤ A.finiteLocalNorm v

def FinitePlaceNontrivialTameAt
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) : Prop :=
  finiteUnitFiltration v 1 ≤ A.finiteLocalNorm v ∧
    ¬finiteUnitFiltration v 0 ≤ A.finiteLocalNorm v

def FinitePlaceWildAt
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) : Prop :=
  ¬finiteUnitFiltration v 1 ≤ A.finiteLocalNorm v

theorem extensionConductorExponent_zero_iff_unramified
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    extensionConductorExponent A v = 0 ↔ FinitePlaceUnramifiedAt A v := by
  sorry

theorem extensionConductorExponent_one_iff_nontrivial_tame
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    extensionConductorExponent A v = 1 ↔ FinitePlaceNontrivialTameAt A v := by
  sorry

theorem extensionConductorExponent_ge_two_iff_wild
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    2 ≤ extensionConductorExponent A v ↔ FinitePlaceWildAt A v := by
  sorry

/-! `A.finiteLocalNorm` is the local norm interface.  The following bridges
state the usual local interpretation of the three cases and are left for the
global Artin/norm theorem from the preceding chapters. -/

theorem extensionConductorExponent_zero_iff_local_norm_is_unramified
    (A : AbelianArtinData (K := K) (I := I) D G)
    (v : NumberField.FinitePlace K) :
    extensionConductorExponent A v = 0 ↔
      finiteUnitFiltration v 0 ≤ A.finiteLocalNorm v := by
  sorry

def ExtensionConductorBound
    (A : AbelianArtinData (K := K) (I := I) D G) (m : Modulus K) : Prop :=
  (∀ v : NumberField.FinitePlace K,
    extensionConductorExponent A v ≤ m.finiteExponent v) ∧
    (∀ v : RealPlace K, A.complexified v → v ∈ m.infinitePart)

theorem extensionConductor_is_least_modulus
    (A : AbelianArtinData (K := K) (I := I) D G) (m : Modulus K) :
    extensionConductor A ≤ m ↔ ExtensionConductorBound A m := by
  sorry

theorem ray_units_are_killed_by_an_extension_conductor_bound
    (A : AbelianArtinData (K := K) (I := I) D G) (m : Modulus K)
    (h : ExtensionConductorBound A m) :
    rayClassSubgroup D m ≤ artinKernel A := by
  sorry

theorem ray_ideles_are_killed_by_an_extension_conductor_bound
    (A : AbelianArtinData (K := K) (I := I) D G) (m : Modulus K)
    (h : ExtensionConductorBound A m) :
    rayIdeleSubgroup D m ≤ A.artin.ker := by
  sorry

theorem ray_ideles_are_killed_when_the_conductor_divides
    (A : AbelianArtinData (K := K) (I := I) D G) (m : Modulus K)
    (h : extensionConductor A ≤ m) :
    rayIdeleSubgroup D m ≤ A.artin.ker := by
  exact ray_ideles_are_killed_by_an_extension_conductor_bound A m
    ((extensionConductor_is_least_modulus A m).mp h)

/-! ### Finite-order idele class characters -/

structure FiniteOrderIdeleClassCharacter (D : IdeleContext K I) where
  toHom : ideleClassGroup D →* ℂˣ
  finiteOrder : ∃ n : ℕ, 0 < n ∧ ∀ c, (toHom c) ^ n = 1
  continuous : Continuous toHom
  finiteConductor_support :
    ∃ S : Finset (NumberField.FinitePlace K),
      ∀ {v : NumberField.FinitePlace K}, v ∉ S →
        ∀ u, u ∈ finiteUnitFiltration v 0 →
          toHom ((ideleClassQuotient D) ((D.finiteComponent v) u)) = 1
  finiteConductor_nonempty :
    ∀ v : NumberField.FinitePlace K,
      Set.Nonempty {n : ℕ |
        ∀ u, u ∈ finiteUnitFiltration v n →
          toHom ((ideleClassQuotient D) ((D.finiteComponent v) u)) = 1}

def localCharacterAtFinite
    (χ : FiniteOrderIdeleClassCharacter D)
    (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ :=
  χ.toHom.comp ((ideleClassQuotient D).comp (D.finiteComponent v))

def localCharacterAtInfinite
    (χ : FiniteOrderIdeleClassCharacter D)
    (v : NumberField.InfinitePlace K) : v.Completionˣ →* ℂˣ :=
  χ.toHom.comp ((ideleClassQuotient D).comp (D.infiniteComponent v))

def characterFiniteExponent
    (χ : FiniteOrderIdeleClassCharacter D)
    (v : NumberField.FinitePlace K) : ℕ :=
  sInf {n : ℕ | ∀ u, u ∈ finiteUnitFiltration v n → localCharacterAtFinite χ v u = 1}

theorem characterFiniteExponent_is_least
    (χ : FiniteOrderIdeleClassCharacter D)
    (v : NumberField.FinitePlace K) :
    (∀ u, u ∈ finiteUnitFiltration v (characterFiniteExponent χ v) →
      localCharacterAtFinite χ v u = 1) ∧
      ∀ n, (∀ u, u ∈ finiteUnitFiltration v n → localCharacterAtFinite χ v u = 1) →
        characterFiniteExponent χ v ≤ n := by
  sorry

def characterUsesRealPlace
    (χ : FiniteOrderIdeleClassCharacter D) (v : RealPlace K) : Prop :=
  localCharacterAtInfinite χ v.1 (-1 : v.1.Completionˣ) ≠ 1

noncomputable def characterConductorIdeal
    (χ : FiniteOrderIdeleClassCharacter D) : Ideal (𝓞 K) :=
  ∏ᶠ v : NumberField.FinitePlace K,
    v.maximalIdeal.asIdeal ^ characterFiniteExponent χ v

theorem characterConductorIdeal_ne_bot
    (χ : FiniteOrderIdeleClassCharacter D) :
    characterConductorIdeal χ ≠ ⊥ := by
  sorry

noncomputable def characterConductor
    (χ : FiniteOrderIdeleClassCharacter D) : Modulus K := by
  classical
  exact
    { finitePart := characterConductorIdeal χ
      finitePart_ne_bot := characterConductorIdeal_ne_bot χ
      infinitePart := Finset.univ.filter (characterUsesRealPlace χ) }

theorem characterConductor_finiteExponent
    (χ : FiniteOrderIdeleClassCharacter D)
    (v : NumberField.FinitePlace K) :
    (characterConductor χ).finiteExponent v = characterFiniteExponent χ v := by
  sorry

theorem characterConductor_real_iff
    (χ : FiniteOrderIdeleClassCharacter D) (v : RealPlace K) :
    v ∈ (characterConductor χ).infinitePart ↔ characterUsesRealPlace χ v := by
  simp [characterConductor]

/-! The group-character presentation of the characters of a finite abelian
extension. -/

def extensionGroupCharacter (A : AbelianArtinData (K := K) (I := I) D G)
    (θ : G →* ℂˣ) : FiniteOrderIdeleClassCharacter D := by
  refine
    { toHom := θ.comp A.classArtin
      finiteOrder := ?_
      continuous := ?_
      finiteConductor_support := ?_
      finiteConductor_nonempty := ?_ }
  · sorry
  · exact A.classArtin_character_continuous θ
  · sorry
  · intro v
    sorry

def extensionCharacterConductor
    (A : AbelianArtinData (K := K) (I := I) D G) (θ : G →* ℂˣ) : Modulus K :=
  characterConductor (extensionGroupCharacter A θ)

theorem extensionConductor_is_lcm_of_character_conductors
    (A : AbelianArtinData (K := K) (I := I) D G) :
    (∀ θ : G →* ℂˣ, extensionCharacterConductor A θ ≤ extensionConductor A) ∧
      (∀ m : Modulus K,
        (∀ θ : G →* ℂˣ, extensionCharacterConductor A θ ≤ m) →
          extensionConductor A ≤ m) := by
  sorry

theorem intersection_of_extension_character_kernels_is_trivial
    (A : AbelianArtinData (K := K) (I := I) D G) :
    (⨅ θ : G →* ℂˣ, θ.ker) = (⊥ : Subgroup G) := by
  sorry

theorem idele_class_character_is_trivial_on_global_principals
    (χ : FiniteOrderIdeleClassCharacter D) (a : Kˣ) :
    χ.toHom (ideleClassQuotient D (D.principal a)) = 1 := by
  sorry

theorem global_units_impose_character_relations
    (χ : FiniteOrderIdeleClassCharacter D) (u : (𝓞 K)ˣ) :
    χ.toHom
        (ideleClassQuotient D
          (D.principal (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))) = 1 := by
  exact idele_class_character_is_trivial_on_global_principals χ _

/-! ### Upper breaks and the shift by one -/

structure LocalUpperRamificationInterface (v : NumberField.FinitePlace K)
    (H : Type*) [Group H] [Fintype H] where
  localArtin : (v.maximalIdeal.adicCompletion K)ˣ →* H
  upperRamification : ℕ → Subgroup H
  local_reciprocity_upper :
    ∀ r, Subgroup.map localArtin (finiteUnitFiltration v r) = upperRamification r

theorem local_reciprocity_maps_unit_filtration_to_upper_ramification
    {H : Type*} [Group H] [Fintype H]
    (v : NumberField.FinitePlace K)
    (R : LocalUpperRamificationInterface v H) (r : ℕ) :
    Subgroup.map R.localArtin (finiteUnitFiltration v r) = R.upperRamification r := by
  exact R.local_reciprocity_upper r

def localConductorExponent
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {n : ℕ | ∀ u, u ∈ finiteUnitFiltration v n → ψ u = 1}

def IsLargestUpperBreak
    (v : NumberField.FinitePlace K)
    (localArtin : (v.maximalIdeal.adicCompletion K)ˣ →* G)
    (ψ : G →* ℂˣ) (b : ℕ) : Prop :=
  (∀ r : ℕ, b < r → ∀ u, u ∈ finiteUnitFiltration v r → ψ (localArtin u) = 1) ∧
    (∃ u, u ∈ finiteUnitFiltration v b ∧ ψ (localArtin u) ≠ 1)

theorem local_character_conductor_eq_upperBreak_add_one
    (v : NumberField.FinitePlace K)
    (localArtin : (v.maximalIdeal.adicCompletion K)ˣ →* G)
    (ψ : G →* ℂˣ) (b : ℕ)
    (h : IsLargestUpperBreak v localArtin ψ b) :
    localConductorExponent v (ψ.comp localArtin) = b + 1 := by
  sorry

theorem local_character_unramified_has_conductor_zero
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ)
    (h : ∀ u, u ∈ finiteUnitFiltration v 0 → ψ u = 1) :
    localConductorExponent v ψ = 0 := by
  sorry

theorem ray_bound_is_upper_break_cutoff
    (v : NumberField.FinitePlace K)
    (localArtin : (v.maximalIdeal.adicCompletion K)ˣ →* G)
    (ψ : G →* ℂˣ) (b : ℕ)
    (h : IsLargestUpperBreak v localArtin ψ b) (n : ℕ) :
    (∀ u, u ∈ finiteUnitFiltration v n → ψ (localArtin u) = 1) ↔ b + 1 ≤ n := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter07
