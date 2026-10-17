module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionModuleMaps

/-! # dg 加群圏上の係数拡大と係数制限の随伴 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma complexCounit_one (K : Complex A') (n : ℤ) (x : K.X n) :
    let := φ.toAlgebra
    ((adjunction φ).counit.app K).f n ((1 : A') ⊗ₜ[A] x) = x :=
  ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ (K.X n) x

lemma moduleUnit_family_naturality (M : RightModule A D) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) ((adjunction φ).unit.app (M.obj y)) =
      (rightRestriction φ D (rightModule φ D M)).map x y ≫
        homPrecompose ((adjunction φ).unit.app (M.obj x))
          ((rightRestriction φ D (rightModule φ D M)).obj y) := by
  let := φ.toAlgebra
  apply closedFamily_of_action A
    (M := M) (N := rightRestriction φ D (rightModule φ D M))
    (fun x => (adjunction φ).unit.app (M.obj x))
  intro x y p r n h f m
  change ((adjunction φ).unit.app (M.obj y)).f n (moduleAction A M f m h) =
    moduleAction A (rightRestriction φ D (rightModule φ D M)) f
      (((adjunction φ).unit.app (M.obj x)).f r m) h
  erw [rightRestriction_action φ D (rightModule φ D M)]
  change (1 : A') ⊗ₜ[A] moduleAction A M f m h =
    moduleAction A' (rightModule φ D M) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h
  exact (rightModule_action φ D M x y p r n h f m).symm

variable [Small.{u} D]

def moduleUnitApp (M : ModuleCategory A D) :
    M ⟶ (moduleRestriction φ D).obj ((moduleExtension φ D).obj M) :=
  moduleMorphismMk A D
    (fun x => (adjunction φ).unit.app ((moduleEvaluation A D x.unop).obj M))
    (moduleUnit_family_naturality φ D (ForgetEnrichment.to (Complex A) M))

@[simp]
lemma moduleUnitApp_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleUnitApp φ D M) =
      (adjunction φ).unit.app ((moduleEvaluation A D x).obj M) :=
  moduleMorphismMk_eval A D _ _ x

set_option maxHeartbeats 800000 in
-- 加群圏の end と二つの係数変更関手の型を展開して自然性を照合する。
def moduleUnit : 𝟭 (ModuleCategory A D) ⟶ moduleExtension φ D ⋙ moduleRestriction φ D where
  app M := moduleUnitApp φ D M
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    erw [moduleUnitApp_eval φ D N x, moduleUnitApp_eval φ D M x]
    change (moduleEvaluation A D x).map f ≫
        (adjunction φ).unit.app ((moduleEvaluation A D x).obj N) =
      (adjunction φ).unit.app ((moduleEvaluation A D x).obj M) ≫
        (moduleEvaluation A D x).map ((moduleRestriction φ D).map ((moduleExtension φ D).map f))
    erw [moduleRestriction_eval φ D ((moduleExtension φ D).map f) x,
      moduleExtension_eval φ D f (show DGBaseChange φ D from x)]
    exact (adjunction φ).unit.naturality ((moduleEvaluation A D x).map f)

omit [Small.{u} D] in
-- Hom と値の二つの係数拡大を純粋生成元に帰着する。
lemma moduleCounit_family_naturality (N : RightModule A' (DGBaseChange φ D))
    (x y : (DGBaseChange φ D)ᵒᵖ) :
    (rightModule φ D (rightRestriction φ D N)).map x y ≫
        homPostcompose ((rightModule φ D (rightRestriction φ D N)).obj x)
          ((adjunction φ).counit.app (N.obj y)) =
      N.map x y ≫ homPrecompose ((adjunction φ).counit.app (N.obj x)) (N.obj y) := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((rightModule φ D (rightRestriction φ D N)).map x y).f p ((1 : A') ⊗ₜ[A] f)).comp
      (Cochain.ofHom ((adjunction φ).counit.app (N.obj y))) (add_zero p) =
    (Cochain.ofHom ((adjunction φ).counit.app (N.obj x))).comp
      ((N.map x y).f p ((1 : A') ⊗ₜ[A] f)) (zero_add p)
  apply Cochain.ext
  intro r n h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((((rightModule φ D (rightRestriction φ D N)).map x y).f p
      ((1 : A') ⊗ₜ[A] f)).comp (Cochain.ofHom ((adjunction φ).counit.app (N.obj y)))
        (add_zero p)).v r n h ((1 : A') ⊗ₜ[A] m) =
    ((Cochain.ofHom ((adjunction φ).counit.app (N.obj x))).comp
      ((N.map x y).f p ((1 : A') ⊗ₜ[A] f)) (zero_add p)).v r n h ((1 : A') ⊗ₜ[A] m)
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  erw [Cochain.ofHom_v, Cochain.ofHom_v]
  change ((adjunction φ).counit.app (N.obj y)).f n
    (moduleAction A' (rightModule φ D (rightRestriction φ D N))
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h) =
    moduleAction A' N ((1 : A') ⊗ₜ[A] f)
      (((adjunction φ).counit.app (N.obj x)).f r ((1 : A') ⊗ₜ[A] m)) h
  erw [rightModule_action φ D (rightRestriction φ D N) x y p r n h f m,
    rightRestriction_action φ D N x y p r n h f m,
    complexCounit_one φ (N.obj y) n, complexCounit_one φ (N.obj x) r m]

def moduleCounitApp (N : ModuleCategory A' (DGBaseChange φ D)) :
    (moduleExtension φ D).obj ((moduleRestriction φ D).obj N) ⟶ N :=
  moduleMorphismMk A' (DGBaseChange φ D)
    (fun x => (adjunction φ).counit.app ((moduleEvaluation A' (DGBaseChange φ D) x.unop).obj N))
    (moduleCounit_family_naturality φ D (ForgetEnrichment.to (Complex A') N))

@[simp]
lemma moduleCounitApp_eval (N : ModuleCategory A' (DGBaseChange φ D)) (x : DGBaseChange φ D) :
    (moduleEvaluation A' (DGBaseChange φ D) x).map (moduleCounitApp φ D N) =
      (adjunction φ).counit.app ((moduleEvaluation A' (DGBaseChange φ D) x).obj N) :=
  moduleMorphismMk_eval A' (DGBaseChange φ D) _ _ x

set_option maxHeartbeats 800000 in
-- 加群圏の end と二つの係数変更関手の型を展開して自然性を照合する。
def moduleCounit : moduleRestriction φ D ⋙ moduleExtension φ D ⟶
    𝟭 (ModuleCategory A' (DGBaseChange φ D)) where
  app N := moduleCounitApp φ D N
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    erw [moduleCounitApp_eval φ D N x, moduleCounitApp_eval φ D M x]
    change (moduleEvaluation A' (DGBaseChange φ D) x).map
        ((moduleExtension φ D).map ((moduleRestriction φ D).map f)) ≫
      (adjunction φ).counit.app ((moduleEvaluation A' (DGBaseChange φ D) x).obj N) =
      (adjunction φ).counit.app ((moduleEvaluation A' (DGBaseChange φ D) x).obj M) ≫
        (moduleEvaluation A' (DGBaseChange φ D) x).map f
    erw [moduleExtension_eval φ D ((moduleRestriction φ D).map f) x,
      moduleRestriction_eval φ D f (show D from x)]
    exact (adjunction φ).counit.naturality ((moduleEvaluation A' (DGBaseChange φ D) x).map f)

set_option maxHeartbeats 800000 in
-- 加群射の等式を各対象の複体随伴の三角恒等式に帰着する。
lemma module_left_triangle (M : ModuleCategory A D) :
    (moduleExtension φ D).map (moduleUnitApp φ D M) ≫
      moduleCounitApp φ D ((moduleExtension φ D).obj M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  erw [moduleExtension_eval φ D (moduleUnitApp φ D M) x,
    moduleUnitApp_eval φ D M (show D from x),
    moduleCounitApp_eval φ D ((moduleExtension φ D).obj M) x]
  exact (adjunction φ).left_triangle_components ((moduleEvaluation A D (show D from x)).obj M)

set_option maxHeartbeats 800000 in
-- 加群射の等式を各対象の複体随伴の三角恒等式に帰着する。
lemma module_right_triangle (N : ModuleCategory A' (DGBaseChange φ D)) :
    moduleUnitApp φ D ((moduleRestriction φ D).obj N) ≫
      (moduleRestriction φ D).map (moduleCounitApp φ D N) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  erw [moduleUnitApp_eval φ D ((moduleRestriction φ D).obj N) x,
    moduleRestriction_eval φ D (moduleCounitApp φ D N) x,
    moduleCounitApp_eval φ D N (show DGBaseChange φ D from x)]
  exact (adjunction φ).right_triangle_components
    ((moduleEvaluation A' (DGBaseChange φ D) (show DGBaseChange φ D from x)).obj N)

/-- 任意の係数変更に対する、全次数自然な右 dg 加群圏上の随伴。 -/
def moduleAdjunction : moduleExtension φ D ⊣ moduleRestriction φ D :=
  Adjunction.mkOfUnitCounit {
    unit := moduleUnit φ D
    counit := moduleCounit φ D
    left_triangle := by
      apply NatTrans.ext
      funext M
      simpa [moduleUnit, moduleCounit] using module_left_triangle φ D M
    right_triangle := by
      apply NatTrans.ext
      funext N
      simpa [moduleUnit, moduleCounit] using module_right_triangle φ D N }

instance moduleExtensionIsLeftAdjoint : (moduleExtension φ D).IsLeftAdjoint :=
  (moduleAdjunction φ D).isLeftAdjoint

instance moduleRestrictionIsRightAdjoint : (moduleRestriction φ D).IsRightAdjoint :=
  (moduleAdjunction φ D).isRightAdjoint

end SerrePositivity.DifferentialGraded.ScalarExtension
