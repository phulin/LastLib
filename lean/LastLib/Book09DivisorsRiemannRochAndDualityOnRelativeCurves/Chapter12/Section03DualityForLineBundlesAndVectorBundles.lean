import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

/-! ### 12.3 Duality for line bundles and vector bundles -/

/-- The degree-one line-bundle form of Serre duality, formula (12.4). -/
theorem chapter12_line_bundle_duality_degree_one
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (L : Chapter04LineBundle C.scheme) :
    Module.Dual k (chapter12HOne K L.sheaf) ≃ₗ[k]
      chapter12HZero K (chapter12LineBundleOmegaTwist W L).sheaf := by
  sorry

/-- The degree-zero line-bundle form of Serre duality, formula (12.4). -/
theorem chapter12_line_bundle_duality_degree_zero
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (L : Chapter04LineBundle C.scheme) :
    Module.Dual k (chapter12HZero K L.sheaf) ≃ₗ[k]
      chapter12HOne K (chapter12LineBundleOmegaTwist W L).sheaf := by
  sorry

/-- Formula (12.5) packaged for each of the two cohomological degrees. -/
theorem chapter12_vector_bundle_duality_degree_one
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C] 
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C) :
    Module.Dual k (chapter12HOne K E.module) ≃ₗ[k]
      chapter12HZero K (chapter12VectorBundleOmegaTwist W E) := by
  sorry

theorem chapter12_vector_bundle_duality_degree_zero
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C) :
    Module.Dual k (chapter12HZero K E.module) ≃ₗ[k]
      chapter12HOne K (chapter12VectorBundleOmegaTwist W E) := by
  sorry

structure Chapter12VectorBundleDualityFamily
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C) where
  degreeZero : Module.Dual k (chapter12HZero K E.module) ≃ₗ[k]
    chapter12HOne K (chapter12VectorBundleOmegaTwist W E)
  degreeOne : Module.Dual k (chapter12HOne K E.module) ≃ₗ[k]
    chapter12HZero K (chapter12VectorBundleOmegaTwist W E)

def chapter12VectorBundleDualityFamily
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C) :
    Chapter12VectorBundleDualityFamily K W E :=
  { degreeZero := chapter12_vector_bundle_duality_degree_zero K W E
    degreeOne := chapter12_vector_bundle_duality_degree_one K W E }

/-! Internal Hom is identified with the tensor expression for locally free
sheaves, and the higher sheaf Ext groups vanish. -/
structure Chapter12VectorBundleInternalHomData
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C)
    [Chapter12InternalHomTheory C.scheme] where
  internalHomIso :
    chapter12InternalHom E.module W.omega ≅ chapter12VectorBundleOmegaTwist W E
  higherSheafExtVanishing : ∀ n : ℕ, 0 < n →
    IsZero (chapter12SheafExt E.module W.omega n)

theorem chapter12_vector_bundle_internal_hom_tensor_omega
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C)
    [Chapter12InternalHomTheory C.scheme] :
    Nonempty (Chapter12VectorBundleInternalHomData K W E) := by
  sorry

theorem chapter12_vector_bundle_internal_hom_identification
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C)
    [Chapter12InternalHomTheory C.scheme]
    (I : Chapter12VectorBundleInternalHomData K W E) :
    chapter12InternalHom E.module W.omega ≅ chapter12VectorBundleOmegaTwist W E :=
  I.internalHomIso

theorem chapter12_vector_bundle_higher_sheaf_ext_vanishing
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C)
    [Chapter12InternalHomTheory C.scheme]
    (I : Chapter12VectorBundleInternalHomData K W E)
    (n : ℕ) (hn : 0 < n) : IsZero (chapter12SheafExt E.module W.omega n) :=
  I.higherSheafExtVanishing n hn

/-! For a coherent sheaf the target is Ext, rather than cohomology of the
naive sheaf dual. -/
theorem chapter12_coherent_sheaf_serre_duality_degree_zero
    {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C)
    (T : Chapter12ExtContext C)
    (W : Chapter12DualizingSheafData C K)
    (F : C.scheme.Modules) (hF : chapter12CoherentSheaf F) :
    Module.Dual k (chapter12HZero K F) ≃ₗ[k]
      chapter12Ext T F W.omega 1 := by
  sorry

theorem chapter12_coherent_sheaf_serre_duality_degree_one
    {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C)
    (T : Chapter12ExtContext C)
    (W : Chapter12DualizingSheafData C K)
    (F : C.scheme.Modules) (hF : chapter12CoherentSheaf F) :
    Module.Dual k (chapter12HOne K F) ≃ₗ[k]
      chapter12Ext T F W.omega 0 := by
  sorry

theorem chapter12_coherent_sheaf_serre_duality
    {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C)
    (T : Chapter12ExtContext C)
    (W : Chapter12DualizingSheafData C K)
    (F : C.scheme.Modules) (hF : chapter12CoherentSheaf F)
    (i : Fin 2) :
    Module.Dual k (chapter12H K F (i : ℕ)) ≃ₗ[k]
      chapter12Ext T F W.omega (1 - (i : ℕ)) := by
  sorry

/-- The warning in the text is an explicit predicate: it records that the
Ext target is not being silently identified with the cohomology of a sheaf
dual for a general coherent input. -/
def chapter12_ext_term_not_generally_sheaf_dual
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12InternalHomTheory C.scheme]
    (K : Chapter12CohomologyContext C)
    (T : Chapter12ExtContext C)
    (W : Chapter12DualizingSheafData C K)
    (F : C.scheme.Modules) : Prop :=
  ¬ ∀ i : Fin 2, Nonempty
      (chapter12Ext T F W.omega (1 - (i : ℕ)) ≃ₗ[k]
        chapter12H K (chapter12InternalHom F W.omega) (1 - (i : ℕ)))

/-! Proper Cohen--Macaulay curves use the same Ext statement with their
dualizing sheaf. -/
theorem chapter12_proper_cm_coherent_sheaf_serre_duality
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k)
    (T : Chapter12ProperCMCohomologyContext C)
    (F : C.carrier.Modules) (hF : chapter04FiniteTypeQuasiCoherent F)
    (i : Fin 2) :
    Module.Dual k (T.H F (i : ℕ)) ≃ₗ[k]
      T.Ext F C.dualizing (1 - (i : ℕ)) := by
  sorry

/-! A Gorenstein package makes the dualizing module into a line bundle. -/
structure Chapter12ProperCMGorensteinData
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) where
  omega : Chapter04LineBundle C.carrier
  omega_iso : omega.sheaf ≅ C.dualizing
  dual : Chapter04LineBundle C.carrier → Chapter04LineBundle C.carrier
  dual_involutive : ∀ L, chapter12LineBundleIsomorphic (dual (dual L)) L
  unit : Chapter04LineBundle C.carrier
  dual_tensor_iso_unit : ∀ L, chapter12LineBundleIsomorphic
    (chapter04LineBundleTensor (dual L) L) unit

def chapter12ProperCMGorensteinOmegaTwist
    {k : Type u} [Field k]
    {C : Chapter12ProperCohenMacaulayCurve k}
    (G : Chapter12ProperCMGorensteinData C)
    (L : Chapter04LineBundle C.carrier) : Chapter04LineBundle C.carrier :=
  chapter04LineBundleTensor (G.dual L) G.omega

theorem chapter12_proper_cm_gorenstein_line_bundle_duality_degree_one
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k)
    (T : Chapter12ProperCMCohomologyContext C)
    (G : Chapter12ProperCMGorensteinData C)
    (hG : C.gorenstein)
    (L : Chapter04LineBundle C.carrier) :
    Module.Dual k (T.H L.sheaf 1) ≃ₗ[k]
      T.H (chapter12ProperCMGorensteinOmegaTwist G L).sheaf 0 := by
  sorry

theorem chapter12_proper_cm_gorenstein_line_bundle_duality_degree_zero
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k)
    (T : Chapter12ProperCMCohomologyContext C)
    (G : Chapter12ProperCMGorensteinData C)
    (hG : C.gorenstein)
    (L : Chapter04LineBundle C.carrier) :
    Module.Dual k (T.H L.sheaf 0) ≃ₗ[k]
      T.H (chapter12ProperCMGorensteinOmegaTwist G L).sheaf 1 := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
