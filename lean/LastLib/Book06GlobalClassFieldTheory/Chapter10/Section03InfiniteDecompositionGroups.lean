import LastLib.Book06GlobalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

universe u v w x y z

/-!
## 10.3. Infinite decomposition groups
-/

/- LOCAL_DEPENDENCY_GUESS: a place-level completion embedding and the local
reciprocity map are supplied by the preceding local/global class-field
chapters. The square below records only their functorial interface. -/
structure Chapter10LocalGlobalReciprocitySquare
    (C : Type u) (K : Type v) (Kab : Type w) (Kv : Type x) (Gv : Type y)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
  [Field Kv] [CommGroup Gv]
    (F : Chapter10FiniteArtinFamily C K Kab) where
  /-- The local factor embeds into the idele class group. -/
  localEmbedding : Kvˣ →* C
  localEmbedding_injective : Function.Injective localEmbedding
  localReciprocity : Kvˣ →* Gv
  decompositionMap : Gv →* Gal(Kab / K)
  commutes :
    (decompositionMap.comp localReciprocity) =
      (chapter10GlobalArtinMap F).comp localEmbedding

namespace Chapter10LocalGlobalReciprocitySquare

  variable {C : Type u} {K : Type v} {Kab : Type w} {Kv : Type x} {Gv : Type y}
    [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
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
  exact chapter10_conjugation_disappears_after_abelianization
    (Abelianization.of : D →* Abelianization D) g x

theorem chapter10_decomposition_group_choice_independent_after_abelianization
    {D A : Type u} [Group D] [CommGroup A]
    (q : D →* A) {g₁ g₂ x : D}
    (h : g₂ = g₁ * x * g₁⁻¹) : q g₂ = q x := by
  subst g₂
  exact chapter10_conjugation_disappears_after_abelianization q g₁ x

/- The local units and a finite-place uniformizer are recorded against the
global inertia quotient. -/
structure Chapter10FinitePlaceReciprocityData
    (C : Type u) (K : Type v) (Kab : Type w) (Kv : Type x) (Gv : Type y)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F) where
  /-- The normalized valuation on the local multiplicative group. -/
  valuation : Kvˣ →* Multiplicative ℤ
  uniformizer : Kvˣ
  uniformizer_valuation :
    valuation uniformizer = Multiplicative.ofAdd 1
  globalInertia : Subgroup (Gal(Kab / K))
  [globalInertia_normal : globalInertia.Normal]
  globalInertia_le_decompositionGroup :
    globalInertia ≤ Chapter10LocalGlobalReciprocitySquare.decompositionGroup S
  units_map_to_inertia :
    valuation.ker.map (Chapter10LocalGlobalReciprocitySquare.globalLocalArtin S) ≤ globalInertia
  arithmeticFrobenius : Gal(Kab / K) ⧸ globalInertia
  uniformizer_maps_to_arithmeticFrobenius :
    QuotientGroup.mk' globalInertia
        (Chapter10LocalGlobalReciprocitySquare.globalLocalArtin S uniformizer) =
      arithmeticFrobenius

attribute [instance] Chapter10FinitePlaceReciprocityData.globalInertia_normal

theorem chapter10_units_map_to_global_inertia
    {C : Type u} {K : Type v} {Kab : Type w} {Kv : Type x} {Gv : Type y}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    (P : Chapter10FinitePlaceReciprocityData C K Kab Kv Gv F S) :
    P.valuation.ker.map (Chapter10LocalGlobalReciprocitySquare.globalLocalArtin S) ≤
      P.globalInertia :=
  P.units_map_to_inertia

theorem chapter10_uniformizer_maps_to_arithmetic_frobenius
    {C : Type u} {K : Type v} {Kab : Type w} {Kv : Type x} {Gv : Type y}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    (P : Chapter10FinitePlaceReciprocityData C K Kab Kv Gv F S) :
    QuotientGroup.mk' P.globalInertia
        (Chapter10LocalGlobalReciprocitySquare.globalLocalArtin S P.uniformizer) =
      P.arithmeticFrobenius :=
  P.uniformizer_maps_to_arithmeticFrobenius

/- Complexification at a real place is a second precise compatibility datum;
the square is the only part needed for its formal functoriality. -/
structure Chapter10RealPlaceComplexificationData
    (C : Type u) (K : Type v) (Kab : Type w) (Kv : Type x) (Gv : Type y)
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F)
    (v : NumberField.InfinitePlace K) where
  place_isReal : v.IsReal
  /-- The local complexification is the image of the negative component under
    local reciprocity, rather than an unrelated chosen element. -/
  localComplexification : Gv
  localComplexification_is_negative :
    localComplexification = S.localReciprocity (-1 : Kvˣ)
  globalComplexification : Gal(Kab / K)
  compatible :
    S.decompositionMap localComplexification = globalComplexification

theorem chapter10_real_place_complexification_compatible
    {C : Type u} {K : Type v} {Kab : Type w} {Kv : Type x} {Gv : Type y}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv]
    {F : Chapter10FiniteArtinFamily C K Kab}
    {S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F}
    {v : NumberField.InfinitePlace K}
    (R : Chapter10RealPlaceComplexificationData C K Kab Kv Gv F S v) :
    S.decompositionMap R.localComplexification = R.globalComplexification :=
  R.compatible

/-- Every global character restricts through the local reciprocity square. -/
theorem chapter10_character_restriction_compatibility
    {C : Type u} {K : Type v} {Kab : Type w} {Kv : Type x} {Gv : Type y} {A : Type z}
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [Field K] [Field Kab] [Algebra K Kab] [IsGalois K Kab]
    [Field Kv] [CommGroup Gv] [Monoid A]
    (F : Chapter10FiniteArtinFamily C K Kab)
    (S : Chapter10LocalGlobalReciprocitySquare C K Kab Kv Gv F)
    (χ : Gal(Kab / K) →* A) :
    (χ.comp S.decompositionMap).comp S.localReciprocity =
      (χ.comp (chapter10GlobalArtinMap F)).comp S.localEmbedding := by
  ext x
  change χ (S.decompositionMap (S.localReciprocity x)) =
    χ ((chapter10GlobalArtinMap F) (S.localEmbedding x))
  exact congrArg χ (DFunLike.congr_fun S.commutes x)

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
