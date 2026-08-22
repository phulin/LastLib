import LastLib.Book05LocalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped IsMulCommutative Pointwise

local instance chapter08_isMulCommutative_of_commGroup
    {G : Type*} [CommGroup G] : IsMulCommutative G :=
  IsMulCommutative.of_comm (fun _ _ => mul_comm _ _)

/-! ## 8.2. Units are the abelian inertia group -/

/- The image of a subgroup under a quotient map is kept explicit.  This is
   the book-facing replacement for silently identifying a subgroup with its
   abstract abelianization. -/
def chapter08SubgroupImage
    {G Q : Type*} [Group G] [Group Q]
    (H : Subgroup G) (ρ : G →* Q) : Subgroup Q :=
  H.map ρ

def chapter08InertiaKernel
    {G Q : Type*} [Group G] [Group Q]
    (reduction : G →* Q) : Subgroup G :=
  reduction.ker

def chapter08InertiaImageInAbelianization
    {G A : Type*} [Group G] [Group A]
    (inertia : Subgroup G) (abelianizationMap : G →* A) : Subgroup A :=
  chapter08SubgroupImage inertia abelianizationMap

abbrev Chapter08AbsoluteGaloisGroup (K : Type*) [Field K] :=
  Field.absoluteGaloisGroup K

def chapter08AbsoluteInertia
    {K Q : Type*} [Field K] [Group Q]
    (reduction : Chapter08AbsoluteGaloisGroup K →* Q) :
    Subgroup (Chapter08AbsoluteGaloisGroup K) :=
  reduction.ker

def chapter08AbsoluteInertiaImage
    {K Q A : Type*} [Field K] [Group Q] [Group A]
    (reduction : Chapter08AbsoluteGaloisGroup K →* Q)
    (abelianizationMap : Chapter08AbsoluteGaloisGroup K →* A) : Subgroup A :=
  chapter08InertiaImageInAbelianization
    (chapter08AbsoluteInertia reduction) abelianizationMap

abbrev Chapter08AbsoluteGaloisAbelianization (K : Type*) [Field K] :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05Abelianization
    (Chapter08AbsoluteGaloisGroup K)

def chapter08AbsoluteGaloisAbelianizationMap
    {K : Type*} [Field K] :
    Chapter08AbsoluteGaloisGroup K →*
      Chapter08AbsoluteGaloisAbelianization K :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05AbelianizationMap _

def chapter08AbsoluteInertiaAbelianizationImage
    {K Q : Type*} [Field K] [Group Q]
    (reduction : Chapter08AbsoluteGaloisGroup K →* Q) :
    Subgroup (Chapter08AbsoluteGaloisAbelianization K) :=
  chapter08AbsoluteInertiaImage reduction
    (chapter08AbsoluteGaloisAbelianizationMap (K := K))

theorem chapter08_inertia_image_mem_iff
    {G A : Type*} [Group G] [Group A]
    (I : Subgroup G) (ab : G →* A) (a : A) :
    a ∈ chapter08InertiaImageInAbelianization I ab ↔
      ∃ g : I, ab g = a := by
  sorry

/- The finite-level statement uses the canonical inertia subgroup attached to
   the preserved valuation branch. -/
theorem chapter08_finite_reciprocity_units_eq_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) :
    (chapter08UnitFiltration X.base.valuation 0).map
        (chapter08FiniteReciprocityMap D) =
      chapter08FiniteInertia X := by
  sorry

theorem chapter08_finite_reciprocity_units_are_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    {u : Kˣ} (hu : u ∈ chapter08UnitFiltration X.base.valuation 0) :
    chapter08FiniteReciprocityMap D u ∈ chapter08FiniteInertia X := by
  rw [← chapter08_finite_reciprocity_units_eq_inertia X D]
  exact ⟨u, hu, rfl⟩

/- The infinite image is the kernel of the maximal unramified quotient. -/
theorem chapter08_infinite_reciprocity_units_eq_inertia_image
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation) :
    (chapter08UnitFiltration D.valuation 0).map
        (chapter08LocalReciprocity S) =
      U.quotient.ker := by
  sorry

theorem chapter08_infinite_units_map_subgroup_le_inertia_image
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation) :
    (chapter08UnitFiltration D.valuation 0).map
        (chapter08LocalReciprocity S) ≤
      U.quotient.ker := by
  sorry

def chapter08UnitReciprocityIntoInertia
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hunits :
      (chapter08UnitFiltration D.valuation 0).map
          (chapter08LocalReciprocity S) = U.quotient.ker) :
    chapter08UnitFiltration D.valuation 0 →*
      U.quotient.ker := by
  refine ((chapter08LocalReciprocity S).comp
      (chapter08UnitFiltration D.valuation 0).subtype).codRestrict _ ?_
  intro u
  rw [← hunits]
  exact ⟨u, u.property, rfl⟩

theorem chapter08_units_topologically_isomorphic_to_abelian_inertia
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [TopologicalSpace (Gal(KAb / K))]
    [IsTopologicalGroup (Gal(KAb / K))]
    [T2Space (Gal(KAb / K))]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation)
    (hcompact : IsCompact
      (chapter08UnitFiltration D.valuation 0 : Set Kˣ))
    (hcontinuous : Continuous
      (chapter08UnitReciprocityIntoInertia D S U
        (chapter08_infinite_reciprocity_units_eq_inertia_image D S U
          hvaluation)))
    (hinjective : Function.Injective
      (chapter08UnitReciprocityIntoInertia D S U
        (chapter08_infinite_reciprocity_units_eq_inertia_image D S U
          hvaluation))) :
    Nonempty
      (chapter08UnitFiltration D.valuation 0 ≃ₜ* U.quotient.ker) := by
  sorry

/- The maximal unramified fixed field has norm group
   `π^(f ℤ) · O_Kˣ`. -/
theorem chapter08_maximal_unramified_norm_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (f : ℕ) (hf : f = X.residueDegree) :
    chapter08NormSubgroup K
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField
          (K := K) (L := L) (chapter08FiniteInertia X)) =
      Subgroup.zpowers (X.base.uniformizer ^ f) ⊔
        chapter08Units X.base.valuation := by
  sorry

local instance chapter08_finite_inertia_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) :
    (chapter08FiniteInertia X).Normal := by
  sorry

def chapter08FiniteInertiaQuotientMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) :
    Gal(L / K) →* Gal(L / K) ⧸ chapter08FiniteInertia X :=
  QuotientGroup.mk' (chapter08FiniteInertia X)

theorem chapter08_finite_units_are_in_kernel_of_residue_quotient
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) :
    ∀ u : chapter08UnitFiltration X.base.valuation 0,
      chapter08FiniteInertiaQuotientMap X
        (chapter08FiniteReciprocityMap D u) = 1 := by
  sorry

abbrev chapter08UnitNormQuotient
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Type _ :=
  chapter08UnitFiltration X.base.valuation 0 ⧸
    (chapter08NormUnitSubgroup X.base.valuation X.valuation).comap
      (chapter08UnitFiltration X.base.valuation 0).subtype

abbrev chapter08FieldNormQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Type _ :=
  Kˣ ⧸ chapter08NormSubgroup K L

local instance chapter08_field_norm_subgroup_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (chapter08NormSubgroup K L).Normal := by
  sorry

local instance chapter08_unit_norm_subgroup_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) :
    ((chapter08NormUnitSubgroup X.base.valuation X.valuation).comap
      (chapter08UnitFiltration X.base.valuation 0).subtype).Normal := by
  sorry

def chapter08ValuationModHom
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) (f : ℕ) :
    Kˣ →* Multiplicative (ZMod f) where
  toFun x :=
    Multiplicative.ofAdd
      ((Multiplicative.toAdd (D.coordinate.valuation x) : ℤ) : ZMod f)
  map_one' := by simp
  map_mul' x y := by simp

def chapter08UnitToFieldNormQuotientMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) :
    chapter08UnitNormQuotient X →*
      chapter08FieldNormQuotient K L := by
  let N : Subgroup Kˣ := chapter08NormSubgroup K L
  let U : Subgroup Kˣ := chapter08UnitFiltration X.base.valuation 0
  let N₀ : Subgroup U :=
    (chapter08NormUnitSubgroup X.base.valuation X.valuation).comap U.subtype
  exact QuotientGroup.lift N₀
    ((QuotientGroup.mk' N).comp U.subtype) (by
      intro x hx
      exact (QuotientGroup.eq_one_iff (N := N) x.1).2
        (chapter08_norm_unit_subgroup_le_norm_subgroup
          X.base.valuation X.valuation hx))

def chapter08ValuationQuotientMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) (f : ℕ)
    (hN : chapter08NormSubgroup K L ≤
      (chapter08ValuationModHom X.base f).ker) :
    chapter08FieldNormQuotient K L →*
      Multiplicative (ZMod f) :=
  QuotientGroup.lift (chapter08NormSubgroup K L)
    (chapter08ValuationModHom X.base f) hN

/- The exact diagram is stored as a single source-facing object.  Its three
   equivalences are the vertical arrows; the two `MulExact` fields are the
   top and bottom rows. -/
structure Chapter08UnitInertiaExactSequence
    {K L : Type} {Q : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup Q] [Finite Q]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) (f : ℕ)
    (ρ : Gal(L / K) →* Q) (arithmeticFrobenius : Q)
    (hN : chapter08NormSubgroup K L ≤
      (chapter08ValuationModHom X.base f).ker) where
  unitEquiv : chapter08UnitNormQuotient X ≃* chapter08FiniteInertia X
  fieldEquiv : chapter08FieldNormQuotient K L ≃* Gal(L / K)
  residueEquiv : Multiplicative (ZMod f) ≃* Q
  topExact :
    Function.MulExact
      (chapter08UnitToFieldNormQuotientMap X)
      (chapter08ValuationQuotientMap X f hN) ∧
      Function.Surjective (chapter08ValuationQuotientMap X f hN)
  topInjective :
    Function.Injective (chapter08UnitToFieldNormQuotientMap X)
  bottomExact :
    Function.MulExact (Subgroup.subtype (chapter08FiniteInertia X)) ρ ∧
      Function.Surjective ρ
  bottomInjective :
    Function.Injective (Subgroup.subtype (chapter08FiniteInertia X))
  leftSquare : ∀ x : chapter08UnitNormQuotient X,
    fieldEquiv (chapter08UnitToFieldNormQuotientMap X x) =
      (unitEquiv x : Gal(L / K))
  middleSquare : ∀ x : chapter08FieldNormQuotient K L,
    residueEquiv (chapter08ValuationQuotientMap X f hN x) =
      ρ (fieldEquiv x)
  rightFrobenius :
    residueEquiv (Multiplicative.ofAdd 1) = arithmeticFrobenius

theorem chapter08_unit_inertia_exact_sequence
    {K L : Type} {Q : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [CommGroup Q] [Finite Q]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) (f : ℕ)
    (ρ : Gal(L / K) →* Q) (arithmeticFrobenius : Q)
    (hN : chapter08NormSubgroup K L ≤
      (chapter08ValuationModHom X.base f).ker)
    (hρ : Function.Surjective ρ)
    (hker : ρ.ker = chapter08FiniteInertia X)
    (hdegree : f = X.residueDegree)
    (hf : 0 < f)
    (hcard : Nat.card Q = f)
    (hFrob : arithmeticFrobenius =
      ρ (chapter08FiniteReciprocityMap D X.base.uniformizer)) :
    Nonempty
      (Chapter08UnitInertiaExactSequence X D f ρ arithmeticFrobenius hN) := by
  sorry

theorem chapter08_unit_norm_index_eq_ramification_index
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [CommGroup (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) :
    ((chapter08NormUnitSubgroup X.base.valuation X.valuation).comap
      (chapter08UnitFiltration X.base.valuation 0).subtype).index =
        X.ramificationIndex := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
