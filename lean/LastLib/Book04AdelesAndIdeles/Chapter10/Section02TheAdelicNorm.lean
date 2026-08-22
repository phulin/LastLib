import LastLib.Book04AdelesAndIdeles.Chapter10.Section01TheLocalNormAsAMultiplicativeDeterminant

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators NNReal RestrictedProduct Topology

/-! ## 10.2. The adelic norm -/

namespace Chapter10GlobalNormData

variable {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
  [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]

/-- The `v`-component of the adelic norm. -/
def adelicNormComponent (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) (v : ιK) : Kloc v := by
  exact ∏ w : {w : ιL // d.below w = v},
    d.chapter10LocalNormAt v w (x (w : ιL))

theorem adelicNormComponent_def
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) (v : ιK) :
    d.adelicNormComponent x v =
      ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (x (w : ιL)) := by
  rfl

/-- The component family is integral at almost every base place. -/
theorem adelicNormComponent_eventually_unit
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) :
    ∀ᶠ v in Filter.cofinite, d.adelicNormComponent x v ∈ d.unitK v := by
  sorry

/-- The adelic norm as an element of the restricted product. -/
def adelicNorm
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) :
    lIdeles d → kIdeles d := by
  intro x
  exact ⟨d.adelicNormComponent x,
    d.adelicNormComponent_eventually_unit x⟩

@[simp]
theorem adelicNorm_apply
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) (v : ιK) :
    d.adelicNorm x v = d.adelicNormComponent x v :=
  rfl

/-- Restricted-product functoriality turns the componentwise norm into a
continuous homomorphism of idele groups. -/
def adelicNormHom
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) :
    lIdeles d →* kIdeles d where
  toFun := d.adelicNorm
  map_one' := by
    sorry
  map_mul' := by
    sorry

@[simp]
theorem adelicNormHom_apply
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) :
    d.adelicNormHom x = d.adelicNorm x :=
  rfl

theorem adelicNormHom_component
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : lIdeles d) (v : ιK) :
    d.adelicNormHom x v =
      ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (x (w : ιL)) := by
  rfl

end Chapter10GlobalNormData

open Chapter10GlobalNormData

theorem chapter10_adelic_norm_continuous
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    [∀ v, TopologicalSpace (Kloc v)] [∀ w, TopologicalSpace (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (hKopen : ∀ v, IsOpen (d.unitK v : Set (Kloc v)))
    (hLopen : ∀ w, IsOpen (d.unitL w : Set (Lloc w)))
    (hlocal : ∀ w, Continuous (d.localNorm w)) :
    Continuous (d.adelicNormHom : lIdeles d → kIdeles d) := by
  sorry

theorem chapter10_adelic_norm_is_a_homomorphism
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) :
    ∃ N : lIdeles d →* kIdeles d,
      ∀ x, N x = d.adelicNorm x :=
  ⟨d.adelicNormHom, fun _ => rfl⟩

/-! ### Module normalization and scalar extension -/

theorem chapter10_adelic_norm_preserves_module
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (hlocal : ∀ w y,
      M.localK (d.below w) (d.localNorm w y) = M.localL w y) (x : lIdeles d) :
    M.moduleK (d.adelicNormHom x) = M.moduleL x := by
  sorry

theorem chapter10_adelic_norm_module_identity
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (hlocal : ∀ w y,
      M.localK (d.below w) (d.localNorm w y) = M.localL w y) :
    ∀ x : lIdeles d, M.moduleK (d.adelicNormHom x) = M.moduleL x := by
  intro x
  exact chapter10_adelic_norm_preserves_module d M hlocal x

theorem chapter10_module_value_ne_zero
    {I : Type*} [Group I] (module : I →* ℝ≥0) (x : I) :
    module x ≠ 0 := by
  sorry

/-- The logarithmic degree associated with a positive adelic module. -/
def chapter10AdelicDegree
    {I : Type*} [Group I] (module : I →* ℝ≥0) (x : I) : ℝ :=
  -Real.log (module x : ℝ)

theorem chapter10_adelic_norm_preserves_degree
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (hlocal : ∀ w y,
      M.localK (d.below w) (d.localNorm w y) = M.localL w y) (x : lIdeles d) :
    chapter10AdelicDegree M.moduleK (d.adelicNormHom x) =
      chapter10AdelicDegree M.moduleL x := by
  sorry

/- The degree is a parameter here rather than inferred from an unavailable
global completion package.  In the number-field instance it is `[L : K]`. -/
theorem chapter10_scalar_extension_module_degree_formula
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w))
    (localDegree : ιL → ℕ)
    (degree : ℕ)
    (hdegree : ∀ v,
      ∑ w : {w : ιL // d.below w = v}, localDegree (w : ιL) = degree)
    (hlocal : ∀ w y,
      M.localL w (scalar w y) = M.localK (d.below w) y ^ localDegree w)
    (x : kIdeles d) :
    M.moduleL (chapter10ScalarExtensionHom d scalar hscalar x) =
      M.moduleK x ^ degree := by
  sorry

theorem chapter10_scalar_extension_degree_formula
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w))
    (localDegree : ιL → ℕ)
    (degree : ℕ)
    (hdegree : ∀ v,
      ∑ w : {w : ιL // d.below w = v}, localDegree (w : ιL) = degree)
    (hlocal : ∀ w y,
      M.localL w (scalar w y) = M.localK (d.below w) y ^ localDegree w)
    (x : kIdeles d) :
    chapter10AdelicDegree M.moduleL
        (chapter10ScalarExtensionHom d scalar hscalar x) =
      degree * chapter10AdelicDegree M.moduleK x := by
  sorry

def chapter10NormAndScalarDegreeConvention
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (M : Chapter10AdelicModuleData d)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w))
    (degree : ℕ) : Prop :=
  (∀ x : lIdeles d, M.moduleK (d.adelicNormHom x) = M.moduleL x) ∧
    (∀ x : kIdeles d,
      M.moduleL (chapter10ScalarExtensionHom d scalar hscalar x) =
        M.moduleK x ^ degree)

end
end LastLib.Book04AdelesAndIdeles.Chapter10
