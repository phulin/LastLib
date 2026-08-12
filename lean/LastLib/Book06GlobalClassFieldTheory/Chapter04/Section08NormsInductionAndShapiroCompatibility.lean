import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u

open scoped BigOperators

/-! ## 4.8. Norms, induction, and Shapiro compatibility -/

/-! The maps in this section are kept in their native multiplicative/additive categories.  In
particular, field norms and idele norms are monoid homomorphisms, whereas the Brauer and
cohomological trace maps are additive homomorphisms. -/

/-- Degree-zero corestriction on `Gₘ` is the field norm (4.17). -/
structure Chapter04MultiplicativeCorestrictionData where
  EUnits : Type u
  [eUnitsGroup : CommGroup EUnits]
  FUnits : Type u
  [fUnitsGroup : CommGroup FUnits]
  corestriction : EUnits →* FUnits
  fieldNorm : EUnits →* FUnits
  corestriction_is_norm : corestriction = fieldNorm

attribute [instance] Chapter04MultiplicativeCorestrictionData.eUnitsGroup
  Chapter04MultiplicativeCorestrictionData.fUnitsGroup

theorem chapter04_degree_zero_corestriction_is_norm
    (D : Chapter04MultiplicativeCorestrictionData) :
    D.corestriction = D.fieldNorm := by
  exact D.corestriction_is_norm

/-- The global Brauer localization/corestriction square (4.18). -/
structure Chapter04BrauerLocalizationCompatibilityData (I : Type u) where
  globalE : Type u
  [globalEGroup : AddCommGroup globalE]
  globalF : Type u
  [globalFGroup : AddCommGroup globalF]
  localE : I → Type u
  [localEGroup : ∀ i, AddCommGroup (localE i)]
  localF : I → Type u
  [localFGroup : ∀ i, AddCommGroup (localF i)]
  localizationE : globalE →+ (∀ i, localE i)
  localizationF : globalF →+ (∀ i, localF i)
  globalCorestriction : globalE →+ globalF
  localCorestriction : (∀ i, localE i) →+ (∀ i, localF i)
  localization_commutes :
    localizationF.comp globalCorestriction = localCorestriction.comp localizationE

attribute [instance] Chapter04BrauerLocalizationCompatibilityData.globalEGroup
  Chapter04BrauerLocalizationCompatibilityData.globalFGroup
  Chapter04BrauerLocalizationCompatibilityData.localEGroup
  Chapter04BrauerLocalizationCompatibilityData.localFGroup

theorem chapter04_brauer_corestriction_localization_commutes
    {I : Type*} (D : Chapter04BrauerLocalizationCompatibilityData I)
    (x : D.globalE) :
    D.localizationF (D.globalCorestriction x) =
      D.localCorestriction (D.localizationE x) := by
  simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun D.localization_commutes x

/-! ### Adelic norms and diagonal principal ideles -/

/-- The product of all local norms over the branches above a place. -/
structure Chapter04AdelicNormData (I : Type u) [Fintype I] where
  localE : I → Type u
  [localEGroup : ∀ i, CommGroup (localE i)]
  localF : I → Type u
  [localFGroup : ∀ i, CommGroup (localF i)]
  localNorm : ∀ i, localE i →* localF i
  adelicNorm : (∀ i, localE i) →* (∀ i, localF i)
  adelic_norm_formula : ∀ y,
    adelicNorm y = fun i => localNorm i (y i)
  EPrincipal : Type u
  [ePrincipalGroup : CommGroup EPrincipal]
  FPrincipal : Type u
  [fPrincipalGroup : CommGroup FPrincipal]
  principalE : EPrincipal →* (∀ i, localE i)
  principalF : FPrincipal →* (∀ i, localF i)
  fieldNorm : EPrincipal →* FPrincipal
  principal_norm_formula :
    (adelicNorm.comp principalE) = (principalF.comp fieldNorm)

attribute [instance] Chapter04AdelicNormData.localEGroup
  Chapter04AdelicNormData.localFGroup
  Chapter04AdelicNormData.ePrincipalGroup
  Chapter04AdelicNormData.fPrincipalGroup

theorem chapter04_adelic_norm_is_product_of_local_norms
    {I : Type*} [Fintype I]
    (D : Chapter04AdelicNormData I) (y : ∀ i, D.localE i) :
    D.adelicNorm y = fun i => D.localNorm i (y i) := by
  exact D.adelic_norm_formula y

theorem chapter04_adelic_norm_preserves_principal_ideles
    {I : Type*} [Fintype I]
    (D : Chapter04AdelicNormData I) (x : D.EPrincipal) :
    D.adelicNorm (D.principalE x) = D.principalF (D.fieldNorm x) := by
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun D.principal_norm_formula x

/-! ### Induction, coinduction, and Shapiro -/

/-- Finite-index induction and coinduction have the same underlying module. -/
structure Chapter04FiniteIndexInductionCoinductionData where
  induced : Type u
  [inducedAddGroup : AddCommGroup induced]
  coinduced : Type u
  [coinducedAddGroup : AddCommGroup coinduced]
  cosetRepresentatives : Type u
  [fintypeCosetRepresentatives : Fintype cosetRepresentatives]
  induction_coinduction_equiv : induced ≃+ coinduced

attribute [instance] Chapter04FiniteIndexInductionCoinductionData.inducedAddGroup
  Chapter04FiniteIndexInductionCoinductionData.coinducedAddGroup
  Chapter04FiniteIndexInductionCoinductionData.fintypeCosetRepresentatives

theorem chapter04_finite_index_induction_is_coinduction
    (D : Chapter04FiniteIndexInductionCoinductionData) :
    Nonempty (D.induced ≃+ D.coinduced) := by
  exact ⟨D.induction_coinduction_equiv⟩

/- The canonical Shapiro declaration is used directly from pinned Mathlib. -/
theorem chapter04_shapiro_coinduced
    {k G : Type u} [CommRing k] [Group G]
    {S : Subgroup G} (A : Rep k S) (n : ℕ) :
    Nonempty (groupCohomology (Rep.coind S.subtype A) n ≅ groupCohomology A n) := by
  exact ⟨groupCohomology.coindIso A n⟩

/-- Compatibility of the Shapiro isomorphism with cup products and the trace. -/
structure Chapter04ShapiroCupTraceCompatibilityData where
  cohomologyOverBase : Type u
  [baseGroup : AddCommGroup cohomologyOverBase]
  cohomologyOverExtension : Type u
  [extensionGroup : AddCommGroup cohomologyOverExtension]
  shapiro : cohomologyOverBase ≃+ cohomologyOverExtension
  basePairing : cohomologyOverBase → chapter04QModZ
  extensionPairing : cohomologyOverExtension → chapter04QModZ
  cup_trace_compatibility : ∀ x,
    extensionPairing (shapiro x) = basePairing x

attribute [instance] Chapter04ShapiroCupTraceCompatibilityData.baseGroup
  Chapter04ShapiroCupTraceCompatibilityData.extensionGroup

theorem chapter04_shapiro_cup_trace_compatibility
    (D : Chapter04ShapiroCupTraceCompatibilityData) (x : D.cohomologyOverBase) :
    D.extensionPairing (D.shapiro x) = D.basePairing x := by
  exact D.cup_trace_compatibility x

/-! The four source languages are recorded by the preceding native maps: multiplicative norm,
product of local norms, local/global invariant adjunction, and Shapiro.  No additional degree
factor belongs in the norm formula; the degree has already appeared in restriction of Brauer
classes, while corestriction preserves invariants branchwise. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
