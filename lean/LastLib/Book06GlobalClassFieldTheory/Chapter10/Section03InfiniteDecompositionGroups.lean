import LastLib.Book06GlobalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

universe u

/-!
## 10.3. Infinite decomposition groups
-/

/- LOCAL_DEPENDENCY_GUESS: a place-level completion embedding and the local
reciprocity map are supplied by the preceding local/global class-field
chapters. The square below records only their functorial interface. -/
structure Chapter10LocalGlobalReciprocitySquare
    (C K Kab Kv Gv : Type u)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    (F : Chapter10FiniteArtinFamily C K Kab) where
  localEmbedding : Kvˣ →* C
  localReciprocity : Kvˣ →* Gv
  decompositionMap : Gv →* Gal(Kab / K)
  decompositionMap_injective : Function.Injective decompositionMap
  commutes :
    (decompositionMap.comp localReciprocity) =
      (chapter10GlobalArtinMap F).comp localEmbedding

namespace Chapter10LocalGlobalReciprocitySquare

variable {C K Kab Kv Gv : Type u}
  [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
  [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
  [Field Kv] [Group Gv]
  {F : Chapter10FiniteArtinFamily C K Kab}

def globalLocalArtin
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) :
    Kvˣ →* Gal(Kab / K) :=
  S.decompositionMap.comp S.localReciprocity

def decompositionGroup
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) :
    Subgroup (Gal(Kab / K)) :=
  S.decompositionMap.range

theorem commutative_square
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) :
    (S.decompositionMap.comp S.localReciprocity) =
      (chapter10GlobalArtinMap F).comp S.localEmbedding := by
  exact S.commutes

theorem local_map_identifies_decomposition_group
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) :
    Function.Injective S.decompositionMap :=
  S.decompositionMap_injective

end Chapter10LocalGlobalReciprocitySquare

/-- A commutative target forgets conjugation. This is the abelianized form of
independence from the choice of an embedding of separable closures. -/
theorem chapter10_conjugation_disappears_after_abelianization
    {D A : Type u} [Group D] [CommGroup A]
    (q : D →* A) (g x : D) :
    q (g * x * g⁻¹) = q x := by
  simp [map_mul, map_inv]

theorem chapter10_abelianization_conjugation
    {D : Type u} [Group D] (g x : D) :
    Abelianization.of (g * x * g⁻¹) = Abelianization.of x := by
  sorry

theorem chapter10_decomposition_group_choice_independent_after_abelianization
    {D A : Type u} [Group D] [CommGroup A]
    (q : D →* A) {g₁ g₂ x : D}
    (h : g₂ = g₁ * x * g₁⁻¹) : q g₂ = q x := by
  subst g₂
  exact chapter10_conjugation_disappears_after_abelianization q g₁ x

/- The local units and a finite-place uniformizer are recorded against the
global inertia quotient. -/
structure Chapter10FinitePlaceReciprocityData
    (C K Kab Kv Gv : Type u)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) where
  localUnits : Subgroup Kvˣ
  uniformizer : Kvˣ
  globalInertia : Subgroup (Gal(Kab / K))
  [globalInertia_normal : globalInertia.Normal]
  units_map_to_inertia :
    localUnits.map S.globalLocalArtin ≤ globalInertia
  arithmeticFrobenius : Gal(Kab / K) ⧸ globalInertia
  uniformizer_maps_to_arithmeticFrobenius :
    QuotientGroup.mk' globalInertia (S.globalLocalArtin uniformizer) =
      arithmeticFrobenius

attribute [instance] Chapter10FinitePlaceReciprocityData.globalInertia_normal

theorem chapter10_units_map_to_global_inertia
    {C K Kab Kv Gv : Type u}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    (P : Chapter10FinitePlaceReciprocityData C K Kab Kv Gv F S) :
    P.localUnits.map S.globalLocalArtin ≤ P.globalInertia :=
  P.units_map_to_inertia

theorem chapter10_uniformizer_maps_to_arithmetic_frobenius
    {C K Kab Kv Gv : Type u}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    (P : Chapter10FinitePlaceReciprocityData C K Kab Kv Gv F S) :
    QuotientGroup.mk' P.globalInertia (S.globalLocalArtin P.uniformizer) =
      P.arithmeticFrobenius :=
  P.uniformizer_maps_to_arithmeticFrobenius

/- Complexification at a real place is a second precise compatibility datum;
the square is the only part needed for its formal functoriality. -/
structure Chapter10RealPlaceComplexificationData
    (C K Kab Kv Gv : Type u)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) where
  localComplexification : ∀ v : NumberField.InfinitePlace K, v.IsReal → Gv
  globalComplexification :
    ∀ v : NumberField.InfinitePlace K, v.IsReal → Gal(Kab / K)
  compatible : ∀ (v : NumberField.InfinitePlace K) (hv : v.IsReal),
    S.decompositionMap (localComplexification v hv) = globalComplexification v hv

theorem chapter10_real_place_complexification_compatible
    {C K Kab Kv Gv : Type u}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    (R : Chapter10RealPlaceComplexificationData C K Kab Kv Gv F S)
    (v : NumberField.InfinitePlace K) (hv : v.IsReal) :
    S.decompositionMap (R.localComplexification v hv) = R.globalComplexification v hv :=
  R.compatible v hv

/-- Every global character restricts through the local reciprocity square. -/
theorem chapter10_character_restriction_compatibility
    {C K Kab Kv Gv A : Type u}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [Group Gv] [Monoid A]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F)
    (χ : Gal(Kab / K) →* A) :
    (χ.comp S.decompositionMap).comp S.localReciprocity =
      (χ.comp (chapter10GlobalArtinMap F)).comp S.localEmbedding := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
