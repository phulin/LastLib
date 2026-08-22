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
  have hbad : Set.Finite {w : ιL | x w ∉ d.unitL w} :=
    Filter.eventually_cofinite.mp x.eventually
  have hbadBelow : Set.Finite (d.below '' {w : ιL | x w ∉ d.unitL w}) :=
    hbad.image d.below
  filter_upwards [hbadBelow.compl_mem_cofinite] with v hv
  apply Subgroup.prod_mem (d.unitK v)
  intro w hw
  have hxw : x (w : ιL) ∈ d.unitL (w : ιL) := by
    by_contra hnot
    apply hv
    exact ⟨(w : ιL), hnot, w.property⟩
  have hmap := d.mapsUnit (w : ιL) hxw
  change cast (congrArg Kloc w.property)
      (d.localNorm (w : ιL) (x (w : ιL))) ∈ d.unitK v
  have transport (v : ιK) (w : {w : ιL // d.below w = v})
      (z : Kloc (d.below (w : ιL)))
      (hz : z ∈ d.unitK (d.below (w : ιL))) :
      cast (congrArg Kloc w.property) z ∈ d.unitK v := by
    cases w with
    | mk w h =>
      cases h
      exact hz
  exact transport v w _ hmap

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
    ext v
    change (∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w (1 : Lloc (w : ιL))) = 1
    apply Finset.prod_eq_one
    intro w hw
    rcases w with ⟨w, rfl⟩
    simp [chapter10LocalNormAt]
  map_mul' := by
    intro x y
    ext v
    change (∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w (x (w : ιL) * y (w : ιL))) =
      (∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (x (w : ιL))) *
        ∏ w : {w : ιL // d.below w = v},
          d.chapter10LocalNormAt v w (y (w : ιL))
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w hw
    rcases w with ⟨w, rfl⟩
    simp [chapter10LocalNormAt]

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
    [∀ v, IsTopologicalGroup (Kloc v)] [∀ w, IsTopologicalGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (hKopen : ∀ v, IsOpen (d.unitK v : Set (Kloc v)))
    (hLopen : ∀ w, IsOpen (d.unitL w : Set (Lloc w)))
    (hlocal : ∀ w, Continuous (d.localNorm w)) :
    Continuous (d.adelicNormHom : lIdeles d → kIdeles d) := by
  have _hKopen := hKopen
  have _hLopen := hLopen
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  have hSc : Sᶜ.Finite :=
    Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  let T : Set ιK :=
    {v | ∀ w : {w : ιL // d.below w = v}, (w : ιL) ∈ S}
  have hTc : Tᶜ.Finite := by
    apply (hSc.image d.below).subset
    intro v hv
    have hv' : ¬ ∀ w : {w : ιL // d.below w = v}, (w : ιL) ∈ S := by
      simpa [T] using hv
    rcases not_forall.mp hv' with ⟨w, hw⟩
    exact ⟨(w : ιL), hw, w.property⟩
  have hT : Filter.cofinite ≤ Filter.principal T :=
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr hTc)
  let gS :
      (Πʳ w, [Lloc w, d.unitL w]_[Filter.principal S]) →
        (Πʳ v, [Kloc v, d.unitK v]_[Filter.principal T]) := fun z =>
    ⟨fun v => ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (z (w : ιL)), by
      filter_upwards [Filter.eventually_principal.mpr (fun v hv => hv)] with v hv
      apply Subgroup.prod_mem (d.unitK v)
      intro w hw
      have hwS : (w : ιL) ∈ S := hv w
      have hzw : z (w : ιL) ∈ d.unitL (w : ιL) :=
        Filter.eventually_principal.mp z.2 (w : ιL) hwS
      have hmap := d.mapsUnit (w : ιL) hzw
      change cast (congrArg Kloc w.property)
          (d.localNorm (w : ιL) (z (w : ιL))) ∈ d.unitK v
      have transport (v : ιK) (w : {w : ιL // d.below w = v})
          (z : Kloc (d.below (w : ιL)))
          (hz : z ∈ d.unitK (d.below (w : ιL))) :
          cast (congrArg Kloc w.property) z ∈ d.unitK v := by
        cases w with
        | mk w h =>
          cases h
          exact hz
      exact transport v w _ hmap⟩
  have hgS : Continuous gS := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    change Continuous (fun z :
        (Πʳ w, [Lloc w, d.unitL w]_[Filter.principal S]) =>
      ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (z (w : ιL)))
    apply continuous_finsetProd Finset.univ
    intro w hw
    rcases w with ⟨w, rfl⟩
    change Continuous (fun z :
        (Πʳ w, [Lloc w, d.unitL w]_[Filter.principal S]) =>
      d.localNorm w (z w))
    exact (hlocal w).comp
      (RestrictedProduct.continuous_eval
        (R := Lloc) (A := fun w => (d.unitL w : Set (Lloc w)))
        (𝓕 := Filter.principal S) w)
  have hfactor :
      d.adelicNormHom ∘
          RestrictedProduct.inclusion Lloc
            (fun w => (d.unitL w : Set (Lloc w))) hS =
        RestrictedProduct.inclusion Kloc
            (fun v => (d.unitK v : Set (Kloc v))) hT ∘ gS := by
    funext z
    apply RestrictedProduct.ext
    intro v
    rfl
  rw [hfactor]
  exact (RestrictedProduct.continuous_inclusion hT).comp hgS

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
  classical
  have hsupport : Function.HasFiniteMulSupport
      (fun w : ιL => M.localL w (x w)) := by
    rw [Function.HasFiniteMulSupport]
    apply Filter.eventually_cofinite.mp
    filter_upwards [x.2] with w hw
    exact M.localL_unit w ⟨x w, hw⟩
  have hfactor (v : ιK) :
      M.localK v (d.adelicNormHom x v) =
        ∏ w : {w : ιL // d.below w = v}, M.localL w (x (w : ιL)) := by
    change M.localK v (∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w (x (w : ιL))) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro w hw
    rcases w with ⟨w, rfl⟩
    exact hlocal w (x w)
  rw [M.moduleK_factorization, M.moduleL_factorization]
  simp_rw [hfactor]
  let s : Finset ιL := hsupport.toFinset
  have hinner (v : ιK) :
      (∏ w : {w : ιL // d.below w = v}, M.localL w (x (w : ιL))) =
        ∏ w ∈ s with d.below w = v, M.localL w (x w) := by
    refine Finset.prod_bij_ne_one
      (s := Finset.univ)
      (t := s.filter (fun w => d.below w = v))
      (f := fun w : {w : ιL // d.below w = v} => M.localL w (x (w : ιL)))
      (g := fun w : ιL => M.localL w (x w))
      (i := fun w _ _ => (w : ιL)) ?_ ?_ ?_ ?_
    · intro w hw hne
      exact Finset.mem_filter.mpr ⟨hsupport.mem_toFinset.mpr hne, w.property⟩
    · intro w₁ h₁ hne₁ w₂ h₂ hne₂ heq
      exact Subtype.ext heq
    · intro w hw hne
      exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, hne, rfl⟩
    · intro w hw hne
      rfl
  simp_rw [hinner]
  rw [finprod_prod_filter d.below s (fun w => M.localL w (x w))]
  exact (finprod_eq_prod_of_mulSupport_toFinset_subset
    (fun w : ιL => M.localL w (x w)) hsupport (Finset.Subset.rfl)).symm

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
  have hmul : module x * module x⁻¹ = 1 := by
    rw [← module.map_mul, mul_inv_cancel, module.map_one]
  intro hx
  rw [hx, zero_mul] at hmul
  exact zero_ne_one hmul

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
  simp only [chapter10AdelicDegree]
  rw [chapter10_adelic_norm_preserves_module d M hlocal x]

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
