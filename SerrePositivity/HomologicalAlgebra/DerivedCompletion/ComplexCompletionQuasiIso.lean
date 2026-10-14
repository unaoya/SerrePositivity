module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion

/-! # 主元Koszul完備化候補の準同型同値不変性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Arrow圏の写像錐は三角形の標準の写像錐射に一致する。 -/
theorem cochainMappingConeFunctor_map_eq
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) :
    (cochainMappingConeFunctor R).map f =
      CochainComplex.mappingCone.map X.hom Y.hom f.left f.right f.w.symm := by
  apply HomologicalComplex.hom_ext
  intro i
  apply CochainComplex.mappingCone.ext_from X.hom (i + 1) i rfl
  · rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_v_desc_f]
    simp [cochainMappingConeFunctor, homotopyCofiber.mapArrowHom,
      homotopyCofiber.inlX_desc_f,
      CochainComplex.mappingCone.inl, homotopyCofiber.inrCompHomotopy_hom,
      Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft]
  · rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_f_desc_f]
    simp [cochainMappingConeFunctor, homotopyCofiber.mapArrowHom,
      CochainComplex.mappingCone.inr,
      homotopyCofiber.inrX_desc_f]

/-- 写像錐の射は、左包含を左側の射へ移す。 -/
theorem cochainMappingConeFunctor_inl
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y) :
    (CochainComplex.mappingCone.inl X.hom).comp
      (CochainComplex.HomComplex.Cochain.ofHom ((cochainMappingConeFunctor R).map f))
      (add_zero (-1 : ℤ)) =
    (CochainComplex.HomComplex.Cochain.ofHom f.left).comp
      (CochainComplex.mappingCone.inl Y.hom) (zero_add (-1 : ℤ)) := by
  rw [cochainMappingConeFunctor_map_eq]
  simp [CochainComplex.mappingCone.map]

/-- 写像錐関手は両端の準同型同値を保つ。 -/
theorem cochainMappingConeFunctor_map_quasiIso
    {X Y : Arrow (CochainComplex (ModuleCat.{u} R) ℤ)} (f : X ⟶ Y)
    [QuasiIso f.left] [QuasiIso f.right] :
    QuasiIso ((cochainMappingConeFunctor R).map f) := by
  rw [cochainMappingConeFunctor_map_eq]
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map
      (CochainComplex.mappingCone.triangleMap X.hom Y.hom f.left f.right f.w.symm))
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (by change IsIso (DerivedCategory.Q.map f.left); infer_instance)
    (by change IsIso (DerivedCategory.Q.map f.right); infer_instance)

/-- 直積のホモロジー比較は各成分の射に自然。 -/
theorem complexTowerProductMap_homology
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (g : ∀ n, K n ⟶ L n)
    (i : ℤ) (x : (piObj K).homology i) (n : ℕ) :
    complexProductHomologyEquiv R L i (homologyMap (complexTowerProductMap R g) i x) n =
      homologyMap (g n) i (complexProductHomologyEquiv R K i x n) := by
  have h := congrArg (fun f ↦ homologyMap f i)
    (complexTowerProductMap_projection R g n)
  simp only [homologyMap_comp] at h
  exact congrArg (fun f ↦ f.hom x) h

/-- 加群複体の可算直積は各成分の準同型同値を保つ。 -/
theorem complexTowerProductMap_quasiIso
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (g : ∀ n, K n ⟶ L n)
    (hg : ∀ n, QuasiIso (g n)) : QuasiIso (complexTowerProductMap R g) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply (complexProductHomologyEquiv R K i).injective
    funext n
    have := hg n
    apply (ConcreteCategory.bijective_of_isIso (homologyMap (g n) i)).1
    simpa only [← complexTowerProductMap_homology] using
      congrArg (fun z ↦ complexProductHomologyEquiv R L i z n) hxy
  · intro y
    have hsurj : ∀ n, Function.Surjective (homologyMap (g n) i) := by
      intro n
      have := hg n
      exact (ConcreteCategory.bijective_of_isIso (homologyMap (g n) i)).2
    choose x hx using fun n ↦ hsurj n (complexProductHomologyEquiv R L i y n)
    refine ⟨(complexProductHomologyEquiv R K i).symm x, ?_⟩
    apply (complexProductHomologyEquiv R L i).injective
    funext n
    rw [complexTowerProductMap_homology, LinearEquiv.apply_symm_apply, hx]

/-- 任意のスカラー錐は係数複体の準同型同値を保つ。 -/
theorem scalarConeFunctor_map_quasiIso (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((scalarConeFunctor a).map f) := by
  let g : Arrow.mk (smulId a K) ⟶ Arrow.mk (smulId a L) :=
    Arrow.homMk f f (by simp [smulId])
  have : QuasiIso g.left := ‹QuasiIso f›
  have : QuasiIso g.right := ‹QuasiIso f›
  exact cochainMappingConeFunctor_map_quasiIso R g

/-- 任意複体の主元Koszul完備化候補は準同型同値を保つ。 -/
theorem complexCompletionFunctor_map_quasiIso (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((complexCompletionFunctor R a).map f) := by
  change QuasiIso
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (CochainComplex.quasiIso_shift_iff _ _).mpr
  have h : QuasiIso ((complexPowerKoszulProductFunctor R a).map f) :=
    complexTowerProductMap_quasiIso R _ (fun n ↦ scalarConeFunctor_map_quasiIso R (a ^ n) f)
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).left) := by
    change QuasiIso ((complexPowerKoszulProductFunctor R a).map f)
    exact h
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).right) := by
    change QuasiIso ((complexPowerKoszulProductFunctor R a).map f)
    exact h
  exact cochainMappingConeFunctor_map_quasiIso R
    ((complexPowerKoszulDifferenceFunctor R a).map f)

end SerrePositivity.DerivedCompletion
