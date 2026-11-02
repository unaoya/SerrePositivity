module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements

/-!
# Tensor.ScalarExtension.BalancedTensor

## 概要
係数変更随伴と balanced tensor の表示・比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarRestrictionModuleMaps（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarRestrictionModuleMaps.lean） -/

/-! # dg 加群圏上の係数制限関手 -/

@[expose] public section ScalarRestrictionModuleMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma rightRestriction_family_naturality {M N : RightModule A' (DGBaseChange φ D)}
    (a : ∀ x : (DGBaseChange φ D)ᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : (DGBaseChange φ D)ᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (rightRestriction φ D M).map x y ≫
        homPostcompose ((rightRestriction φ D M).obj x) ((restriction φ).map (a y)) =
      (rightRestriction φ D N).map x y ≫
        homPrecompose ((restriction φ).map (a x)) ((rightRestriction φ D N).obj y) := by
  rw [rightRestriction_map, rightRestriction_map]
  have hh : (restriction φ).map (M.map x y) ≫ restrictionHom φ (M.obj x) (M.obj y) ≫
      homPostcompose ((restriction φ).obj (M.obj x)) ((restriction φ).map (a y)) =
    ((restriction φ).map (N.map x y) ≫ restrictionHom φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((restriction φ).map (a x)) ((restriction φ).obj (N.obj y)) := by
    erw [← restrictionHom_postcompose φ (M.obj x) (a y)]
    rw [← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp,
      Category.assoc]
    erw [restrictionHom_precompose φ (a x) (N.obj y)]
    exact (Category.assoc _ _ _).symm
  have he := congrArg (fun t => (adjunction φ).unit.app (x ⟶[Complex A] y) ≫ t) hh
  simp only [Category.assoc] at he
  convert he using 1 <;> rfl

variable [Small.{u} D]

/-- 全次数自然な射の値を係数制限し、元の dg 圏上の射に戻す。 -/
def moduleRestrictionMap {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (rightRestriction φ D (ForgetEnrichment.to (Complex A') M)) ⟶
      ForgetEnrichment.of (Complex A) (rightRestriction φ D (ForgetEnrichment.to (Complex A') N)) :=
  moduleMorphismMk A D
    (fun x => (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x.unop).map f))
    (rightRestriction_family_naturality φ D
      (closedTransApp A' (moduleClosedHomEquiv A' (DGBaseChange φ D) M N f))
      (closedTransApp_naturality A' (moduleClosedHomEquiv A' (DGBaseChange φ D) M N f)))

@[simp]
lemma moduleRestrictionMap_eval {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N)
    (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionMap φ D f) =
      (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x).map f) :=
  moduleMorphismMk_eval A D _ _ x

/-- 係数変更の単位に沿った右 dg 加群の係数制限関手。 -/
def moduleRestriction : ModuleCategory A' (DGBaseChange φ D) ⥤ ModuleCategory A D where
  obj M := ForgetEnrichment.of (Complex A)
    (rightRestriction φ D (ForgetEnrichment.to (Complex A') M))
  map f := moduleRestrictionMap φ D f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleRestrictionMap_eval, moduleRestrictionMap_eval]

@[simp]
lemma moduleRestriction_eval {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N)
    (x : D) :
    (moduleEvaluation A D x).map ((moduleRestriction φ D).map f) =
      (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x).map f) :=
  moduleRestrictionMap_eval φ D f x

def moduleRestrictionEvaluationIso (x : D) :
    moduleRestriction φ D ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A' (DGBaseChange φ D) x ⋙ restriction φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarRestrictionModuleMaps

/-! ## ScalarExtensionAdjunction（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionAdjunction.lean） -/

/-! # dg 加群圏上の係数拡大と係数制限の随伴 -/

@[expose] public section ScalarExtensionAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
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
end

end ScalarExtensionAdjunction

/-! ## ScalarExtensionActions（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionActions.lean） -/

/-! # 係数変更と balanced tensor の左右作用 -/

@[expose] public section ScalarExtensionActions
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma leftModule_action (N : LeftModule A D) (x y : D) (p r n : ℤ)
    (h : r + p = n) (f : GradedHom A x y p) (m : (N.obj x).X r) :
    let := φ.toAlgebra
    leftAction A' (leftModule φ D N) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) h =
      (1 : A') ⊗ₜ[A] leftAction A N f m h := by
  let := φ.toAlgebra
  change ((homComparison φ (N.obj x) (N.obj y)).f p
    ((ModuleCat.extendScalars φ).map ((N.map x y).f p) ((1 : A') ⊗ₜ[A] f))).v r n h
      ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, homComparison_apply φ (N.obj x) (N.obj y) p r n h]
  rfl

@[reassoc]
lemma rightAction_comparison (M : RightModule A D) (x y : D) :
    (extension φ).map (BalancedTensor.rightAction A D M x y) =
      (tensorIso φ (M.obj (op y)) (homObject A D x y)).hom ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (M.obj (op y)) (homObject A D x y)
  intro r p h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m f
  change (ModuleCat.extendScalars φ).map ((BalancedTensor.rightAction A D M x y).f n)
    ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op y)) (homObject A D x y) r p n h (m ⊗ₜ[A] f)) =
    (BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y).f n
      ((tensorIso φ (M.obj (op y)) (homObject A D x y)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op y)) (homObject A D x y) r p n h (m ⊗ₜ[A] f)))
  erw [ModuleCat.ExtendScalars.map_tmul φ, BalancedTensor.rightAction_apply,
    cochainTensorBaseChangeIso_apply_ι φ (M.obj (op y)) (homObject A D x y),
    BalancedTensor.rightAction_apply,
    rightModule_action φ D M (op y) (op x) p r n h f m]
  simp only [Units.smul_def, TensorProduct.tmul_smul]
  rfl

@[reassoc]
lemma leftAction_comparison (N : LeftModule A D) (x y : D) :
    (extension φ).map (BalancedTensor.leftAction A D N x y) =
      (tensorIso φ (homObject A D x y) (N.obj x)).hom ≫
        BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (homObject A D x y) (N.obj x)
  intro p r h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f m
  change (ModuleCat.extendScalars φ).map ((BalancedTensor.leftAction A D N x y).f n)
    ((1 : A') ⊗ₜ[A] ιTensorObj (homObject A D x y) (N.obj x) p r n h (f ⊗ₜ[A] m)) =
    (BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y).f n
      ((tensorIso φ (homObject A D x y) (N.obj x)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (homObject A D x y) (N.obj x) p r n h (f ⊗ₜ[A] m)))
  erw [ModuleCat.ExtendScalars.map_tmul φ, BalancedTensor.leftAction_apply,
    cochainTensorBaseChangeIso_apply_ι φ (homObject A D x y) (N.obj x),
    BalancedTensor.leftAction_apply,
    leftModule_action φ D N x y p r n (by omega) f m]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionActions

/-! ## ScalarExtensionPresentation（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionPresentation.lean） -/

/-! # balanced tensor の直和表示の係数変更 -/

@[expose] public section ScalarExtensionPresentation
universe u v
set_option synthInstance.maxHeartbeats 40000

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 三つの tensor 因子の係数変更を左括弧のまま行う。 -/
abbrev tripleIso (K L T : Complex A) := cochainTensorTripleBaseChangeIso φ K L T

lemma tripleIso_hom (K L T : Complex A) :
    (tripleIso φ K L T).hom = (tensorIso φ (K ⊗ L) T).hom ≫
      (tensorIso φ K L).hom ▷ (extension φ).obj T := rfl

/-- 元と同じ対象添字を使う生成項の直和同型。 -/
def generatorIso : (extension φ).obj (BalancedTensor.generators A D M N) ≅
    BalancedTensor.generators A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coproductIso φ (BalancedTensor.objectFamily A D M N) ≪≫
    Sigma.mapIso (fun x : D => tensorIso φ (M.obj (op x)) (N.obj x))

/-- 元と同じ対象対添字を使う関係項の直和同型。 -/
def relationIso : (extension φ).obj (BalancedTensor.relations A D M N) ≅
    BalancedTensor.relations A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coproductIso φ (BalancedTensor.relationFamily A D M N) ≪≫
    Sigma.mapIso (fun xy : D × D => tripleIso φ (M.obj (op xy.2))
      (homObject A D xy.1 xy.2) (N.obj xy.1))

@[reassoc (attr := simp)]
lemma map_ι_generatorIso (x : D) :
    (extension φ).map (Sigma.ι (BalancedTensor.objectFamily A D M N) x) ≫
      (generatorIso φ D M N).hom =
        (tensorIso φ (M.obj (op x)) (N.obj x)).hom ≫
          Sigma.ι (BalancedTensor.objectFamily A' (DGBaseChange φ D)
            (rightModule φ D M) (leftModule φ D N)) x := by
  simp only [generatorIso, Iso.trans_hom, map_ι_coproductIso_assoc,
    Sigma.ι_mapIso_hom]

@[reassoc (attr := simp)]
lemma map_ι_relationIso (xy : D × D) :
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy) ≫
      (relationIso φ D M N).hom =
        (tripleIso φ (M.obj (op xy.2)) (homObject A D xy.1 xy.2) (N.obj xy.1)).hom ≫
          Sigma.ι (BalancedTensor.relationFamily A' (DGBaseChange φ D)
            (rightModule φ D M) (leftModule φ D N)) xy := by
  simp only [relationIso, Iso.trans_hom, map_ι_coproductIso_assoc,
    Sigma.ι_mapIso_hom]

omit [Small.{u} D] in
@[reassoc]
lemma rightRelation_component (x y : D) :
    (extension φ).map (BalancedTensor.rightAction A D M x y ▷ N.obj x) ≫
        (tensorIso φ (M.obj (op x)) (N.obj x)).hom =
      (tripleIso φ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y ▷
          (extension φ).obj (N.obj x) := by
  have hn := tensorIso_naturality φ (BalancedTensor.rightAction A D M x y) (𝟙 (N.obj x))
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hn
  rw [rightAction_comparison φ D M x y, comp_whiskerRight] at hn
  simpa only [tripleIso_hom, Category.assoc] using hn

omit [Small.{u} D] in
@[reassoc]
lemma leftRelation_component (x y : D) :
    (extension φ).map ((α_ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
        M.obj (op y) ◁ BalancedTensor.leftAction A D N x y) ≫
      (tensorIso φ (M.obj (op y)) (N.obj y)).hom =
    (tripleIso φ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
      (α_ ((extension φ).obj (M.obj (op y)))
        ((extension φ).obj (homObject A D x y)) ((extension φ).obj (N.obj x))).hom ≫
          (extension φ).obj (M.obj (op y)) ◁
            BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y := by
  have hn := tensorIso_naturality φ (𝟙 (M.obj (op y))) (BalancedTensor.leftAction A D N x y)
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn,
    leftAction_comparison φ D N x y, whiskerLeft_comp]
  have ha := congrArg (fun f => f ≫ (extension φ).obj (M.obj (op y)) ◁
      BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y)
    (tensorIso_associator φ (M.obj (op y)) (homObject A D x y) (N.obj x)).symm
  simpa only [tripleIso_hom, Category.assoc] using ha

@[reassoc]
lemma relationLeft_square :
    (extension φ).map (BalancedTensor.relationLeft A D M N) ≫ (generatorIso φ D M N).hom =
      (relationIso φ D M N).hom ≫
        BalancedTensor.relationLeft A' (DGBaseChange φ D)
          (rightModule φ D M) (leftModule φ D N) := by
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.relationFamily A D M N)).hom_ext
  intro xy
  change (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _ =
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.relationLeft,
    Sigma.ι_comp_desc, CategoryTheory.Functor.map_comp, Category.assoc, map_ι_generatorIso]
  rw [map_ι_relationIso_assoc, BalancedTensor.relationLeft, Sigma.ι_comp_desc]
  exact rightRelation_component_assoc φ D M N xy.as.1 xy.as.2 _

@[reassoc]
lemma relationRight_square :
    (extension φ).map (BalancedTensor.relationRight A D M N) ≫ (generatorIso φ D M N).hom =
      (relationIso φ D M N).hom ≫
        BalancedTensor.relationRight A' (DGBaseChange φ D)
          (rightModule φ D M) (leftModule φ D N) := by
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.relationFamily A D M N)).hom_ext
  intro xy
  change (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _ =
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.relationRight,
    Sigma.ι_comp_desc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [map_ι_generatorIso]
  rw [map_ι_relationIso_assoc, BalancedTensor.relationRight, Sigma.ι_comp_desc]
  have h := leftRelation_component_assoc φ D M N xy.as.1 xy.as.2
    (Sigma.ι (BalancedTensor.objectFamily A' (DGBaseChange φ D)
      (rightModule φ D M) (leftModule φ D N)) xy.as.2)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h
  convert h using 1; rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionPresentation

/-! ## ScalarExtensionBalanced（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionBalanced.lean） -/

/-! # 相対 balanced tensor の underived 係数変更同型

生成項・関係項の添字は同じ対象および同じ対象対に固定する。
係数環の平坦性は使わず、直和と coequalizer の保存から同型を作る。
-/

@[expose] public section ScalarExtensionBalanced
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 二つの関係射を含む coequalizer 図式全体の同型。 -/
def balancedPresentationIso :
    parallelPair ((extension φ).map (BalancedTensor.relationLeft A D M N))
      ((extension φ).map (BalancedTensor.relationRight A D M N)) ≅
    parallelPair
      (BalancedTensor.relationLeft A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N))
      (BalancedTensor.relationRight A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N)) :=
  parallelPairIso _ _ _ _ (relationIso φ D M N) (generatorIso φ D M N)
    (relationLeft_square φ D M N) (relationRight_square φ D M N)

/-- 任意の環準同型について、相対 tensor と係数拡大は可換する。 -/
def balancedIso : (extension φ).obj (BalancedTensor.obj A D M N) ≅
    BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coequalizerIso φ (BalancedTensor.relationLeft A D M N) (BalancedTensor.relationRight A D M N) ≪≫
    HasColimit.isoOfNatIso (balancedPresentationIso φ D M N)

@[reassoc]
lemma balancedIso_projection :
    (extension φ).map (BalancedTensor.projection A D M N) ≫ (balancedIso φ D M N).hom =
      (generatorIso φ D M N).hom ≫
        BalancedTensor.projection A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) := by
  rw [balancedIso, Iso.trans_hom]
  change (extension φ).map (coequalizer.π _ _) ≫ (coequalizerIso φ _ _).hom ≫ _ = _
  rw [map_π_coequalizerIso_assoc]
  exact HasColimit.ι_isoOfNatIso_hom (balancedPresentationIso φ D M N) WalkingParallelPair.one

@[reassoc (attr := simp)]
lemma balancedIso_ι (x : D) :
    (extension φ).map (BalancedTensor.ι A D M N x) ≫ (balancedIso φ D M N).hom =
      (tensorIso φ (M.obj (op x)) (N.obj x)).hom ≫
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x := by
  rw [BalancedTensor.ι, CategoryTheory.Functor.map_comp, Category.assoc,
    balancedIso_projection, ← Category.assoc, map_ι_generatorIso, Category.assoc]
  rfl

@[reassoc (attr := simp)]
lemma balancedIso_inv_ι (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x ≫
      (balancedIso φ D M N).inv =
      (tensorIso φ (M.obj (op x)) (N.obj x)).inv ≫
        (extension φ).map (BalancedTensor.ι A D M N x) := by
  have h := congrArg (fun t => (tensorIso φ (M.obj (op x)) (N.obj x)).inv ≫ t ≫
    (balancedIso φ D M N).inv) (balancedIso_ι φ D M N x)
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] at h
  exact h.symm

/-- 係数変更後も、元の各対象の生成項の像が射を決める。 -/
lemma extendedBalanced_hom_ext {T : Complex A'}
    {f g : (extension φ).obj (BalancedTensor.obj A D M N) ⟶ T}
    (h : ∀ x : D, (extension φ).map (BalancedTensor.ι A D M N x) ≫ f =
      (extension φ).map (BalancedTensor.ι A D M N x) ≫ g) : f = g := by
  let : Epi ((extension φ).map (BalancedTensor.projection A D M N)) := by
    change Epi ((extension φ).map (coequalizer.π
      (BalancedTensor.relationLeft A D M N) (BalancedTensor.relationRight A D M N)))
    infer_instance
  apply (cancel_epi ((extension φ).map (BalancedTensor.projection A D M N))).1
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.objectFamily A D M N)).hom_ext
  intro x
  have hh := h x.as
  simp only [BalancedTensor.ι, CategoryTheory.Functor.map_comp, Category.assoc] at hh
  convert hh using 1 <;> rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionBalanced

/-! ## ScalarExtensionBalancedNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionBalancedNaturality.lean） -/

/-! # 相対 tensor の係数変更同型の両変数自然性 -/

@[expose] public section ScalarExtensionBalancedNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M M' : RightModule A D} {N N' : LeftModule A D}

omit [Small.{u} D] in
lemma extended_rightAction_family
    (f : ∀ x : D, M.obj (op x) ⟶ M'.obj (op x))
    (hf : ∀ x y, BalancedTensor.rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (homObject A D x y)) ≫ BalancedTensor.rightAction A D M' x y)
    (x y : DGBaseChange φ D) :
    BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y ≫
        (extension φ).map (f x) =
      ((extension φ).map (f y) ⊗ₘ 𝟙 (homObject A' (DGBaseChange φ D) x y)) ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M') x y := by
  apply (cancel_epi (tensorIso φ (M.obj (op y)) (homObject A D x y)).hom).1
  rw [← Category.assoc]
  erw [← rightAction_comparison φ D M x y]
  rw [← CategoryTheory.Functor.map_comp, hf, CategoryTheory.Functor.map_comp]
  erw [rightAction_comparison φ D M' x y]
  have ht := tensorIso_naturality_assoc φ (f y) (𝟙 (homObject A D x y))
    (BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M') x y)
  simp only [CategoryTheory.Functor.map_id] at ht
  convert ht using 1

omit [Small.{u} D] in
lemma extended_leftAction_family
    (g : ∀ x : D, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, BalancedTensor.leftAction A D N x y ≫ g y =
      (𝟙 (homObject A D x y) ⊗ₘ g x) ≫ BalancedTensor.leftAction A D N' x y)
    (x y : DGBaseChange φ D) :
    BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y ≫
        (extension φ).map (g y) =
      (𝟙 (homObject A' (DGBaseChange φ D) x y) ⊗ₘ (extension φ).map (g x)) ≫
        BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N') x y := by
  apply (cancel_epi (tensorIso φ (homObject A D x y) (N.obj x)).hom).1
  rw [← Category.assoc]
  erw [← leftAction_comparison φ D N x y]
  rw [← CategoryTheory.Functor.map_comp, hg, CategoryTheory.Functor.map_comp]
  erw [leftAction_comparison φ D N' x y]
  have ht := tensorIso_naturality_assoc φ (𝟙 (homObject A D x y)) (g x)
    (BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N') x y)
  simp only [CategoryTheory.Functor.map_id] at ht
  convert ht using 1

@[reassoc]
lemma balancedIso_naturality
    (f : ∀ x : D, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x : D, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, BalancedTensor.rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (homObject A D x y)) ≫ BalancedTensor.rightAction A D M' x y)
    (hg : ∀ x y, BalancedTensor.leftAction A D N x y ≫ g y =
      (𝟙 (homObject A D x y) ⊗ₘ g x) ≫ BalancedTensor.leftAction A D N' x y) :
    (extension φ).map (BalancedTensor.mapOfFamilies A D f g hf hg) ≫
        (balancedIso φ D M' N').hom =
      (balancedIso φ D M N).hom ≫
        BalancedTensor.mapOfFamilies A' (DGBaseChange φ D)
          (M := rightModule φ D M) (M' := rightModule φ D M')
          (N := leftModule φ D N) (N' := leftModule φ D N')
          (fun x => (extension φ).map (f x)) (fun x => (extension φ).map (g x))
          (extended_rightAction_family φ D f hf) (extended_leftAction_family φ D g hg) := by
  apply extendedBalanced_hom_ext φ D M N
  intro x
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.ι_mapOfFamilies,
    CategoryTheory.Functor.map_comp, Category.assoc, balancedIso_ι,
    balancedIso_ι_assoc, BalancedTensor.ι_mapOfFamilies]
  exact tensorIso_naturality_assoc φ (f x) (g x) _

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionBalancedNaturality

/-! ## ScalarExtensionLeftMaps（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionLeftMaps.lean） -/

/-! # 左 dg 加群圏の係数拡大と相対 tensor 双関手の比較 -/

@[expose] public section ScalarExtensionLeftMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma leftExtension_family_naturality {M N : LeftModule A D}
    (a : ∀ x : D, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : DGBaseChange φ D) :
    (leftModule φ D M).map x y ≫
        homPostcompose ((leftModule φ D M).obj x) ((extension φ).map (a y)) =
      (leftModule φ D N).map x y ≫
        homPrecompose ((extension φ).map (a x)) ((leftModule φ D N).obj y) := by
  change ((extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y)) ≫
      homPostcompose ((extension φ).obj (M.obj x)) ((extension φ).map (a y)) =
    ((extension φ).map (N.map x y) ≫ homComparison φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((extension φ).map (a x)) ((extension φ).obj (N.obj y))
  rw [Category.assoc, ← homComparison_postcompose φ (M.obj x) (a y),
    ← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp,
    Category.assoc, homComparison_precompose φ (a x) (N.obj y)]
  exact (Category.assoc _ _ _).symm

variable [Small.{u} D]

lemma leftMorphism_hom_naturality {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    (ForgetEnrichment.to (Complex A) M).map x y ≫
        homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
          ((leftModuleEvaluation A D y).map f) =
      (ForgetEnrichment.to (Complex A) N).map x y ≫
        homPrecompose ((leftModuleEvaluation A D x).map f)
          ((ForgetEnrichment.to (Complex A) N).obj y) := by
  have h := closedTransApp_naturality A (leftModuleClosedHomEquiv A D M N f)
    (op (op x)) (op (op y))
  change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) at h
  simpa only [Category.id_comp] using h

def leftModuleExtensionMap {M N : LeftModuleCategory A D} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A') (leftModule φ D (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A') (leftModule φ D (ForgetEnrichment.to (Complex A) N)) :=
  leftModuleMorphismMk A' (DGBaseChange φ D)
    (fun x => (extension φ).map ((leftModuleEvaluation A D x).map f))
    (leftExtension_family_naturality φ D
      (fun x => (leftModuleEvaluation A D x).map f) (leftMorphism_hom_naturality D f))

@[simp]
lemma leftModuleExtensionMap_eval {M N : LeftModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) x).map (leftModuleExtensionMap φ D f) =
      (extension φ).map ((leftModuleEvaluation A D (show D from x)).map f) :=
  leftModuleMorphismMk_eval A' (DGBaseChange φ D) _ _ x

def leftModuleExtension : LeftModuleCategory A D ⥤ LeftModuleCategory A' (DGBaseChange φ D) where
  obj M := ForgetEnrichment.of (Complex A')
    (leftModule φ D (ForgetEnrichment.to (Complex A) M))
  map f := leftModuleExtensionMap φ D f
  map_id M := by
    apply leftModuleMorphism_ext
    intro x
    rw [leftModuleExtensionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply leftModuleMorphism_ext
    intro x
    rw [leftModuleExtensionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      leftModuleExtensionMap_eval, leftModuleExtensionMap_eval]

@[simp]
lemma leftModuleExtension_eval {M N : LeftModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) x).map ((leftModuleExtension φ D).map f) =
      (extension φ).map ((leftModuleEvaluation A D (show D from x)).map f) :=
  leftModuleExtensionMap_eval φ D f x

@[reassoc]
lemma balancedIso_module_naturality {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') :
    (extension φ).map (BalancedTensor.map A D f g) ≫
        (balancedIso φ D (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N')).hom =
      (balancedIso φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N)).hom ≫
        BalancedTensor.map A' (DGBaseChange φ D)
          ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g) := by
  apply extendedBalanced_hom_ext φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  intro x
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.ι_map,
    CategoryTheory.Functor.map_comp, Category.assoc, balancedIso_ι,
    balancedIso_ι_assoc]
  erw [BalancedTensor.ι_map A' (DGBaseChange φ D) ((moduleExtension φ D).map f)
    ((leftModuleExtension φ D).map g) (show DGBaseChange φ D from x)]
  erw [moduleExtension_eval φ D f (show DGBaseChange φ D from x),
    leftModuleExtension_eval φ D g (show DGBaseChange φ D from x)]
  exact tensorIso_naturality_assoc φ ((moduleEvaluation A D x).map f)
    ((leftModuleEvaluation A D x).map g) _

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionLeftMaps

/-! ## ScalarExtensionRing（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionRing.lean） -/

/-! # 一対象環での相対 tensor の係数変更と通常 tensor の比較 -/

@[expose] public section ScalarExtensionRing
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1})

/-- 一対象環の係数変更後の相対 tensor を、値の通常 tensor と比較する。 -/
def ringBalancedIso :
    BalancedTensor.obj A' (DGBaseChange φ PUnit.{1})
        (rightModule φ PUnit.{1} M) (leftModule φ PUnit.{1} N) ≅
      (extension φ).obj (M.obj (op PUnit.unit)) ⊗ (extension φ).obj (N.obj PUnit.unit) :=
  (balancedIso φ PUnit.{1} M N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.ringIso A M N) ≪≫
      tensorIso φ (M.obj (op PUnit.unit)) (N.obj PUnit.unit)

/-- 唯一の対象の生成項を恒等写像へ送る、通常 tensor の標準的比較である。 -/
@[reassoc (attr := simp)]
lemma ι_ringBalancedIso :
    BalancedTensor.ι A' (DGBaseChange φ PUnit.{1})
        (rightModule φ PUnit.{1} M) (leftModule φ PUnit.{1} N) PUnit.unit ≫
      (ringBalancedIso φ M N).hom = 𝟙 _ := by
  simp only [ringBalancedIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    BalancedTensor.ι_ringIso_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

@[reassoc]
lemma ringBalancedIso_comparison :
    (balancedIso φ PUnit.{1} M N).hom ≫ (ringBalancedIso φ M N).hom =
      (extension φ).map (BalancedTensor.ringIso A M N).hom ≫
        (tensorIso φ (M.obj (op PUnit.unit)) (N.obj PUnit.unit)).hom := by
  simp only [ringBalancedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 元の一対象加群が複体から来る場合の、非有界な通常 tensor との比較。 -/
abbrev ringComplexBaseChangeIso (P Q : Complex A) :=
  ringBalancedIso φ (ringModule A P) (ringLeftModule A Q)

lemma ringComplexBaseChange_comparison (P Q : Complex A) :
    (extension φ).map (BalancedTensor.ringComplexTensorIso A P Q).hom ≫
        (cochainTensorBaseChangeIso φ P Q).hom =
      (balancedIso φ PUnit.{1} (ringModule A P) (ringLeftModule A Q)).hom ≫
        (ringComplexBaseChangeIso φ P Q).hom :=
  (ringBalancedIso_comparison φ (ringModule A P) (ringLeftModule A Q)).symm

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionRing

/-! ## ScalarExtensionCoendCoherence（旧 SerrePositivity/DifferentialGraded/Tensor/ScalarExtensionCoendCoherence.lean） -/

/-! # 係数変更と相対 tensor の評価単位・パラメータ結合比較 -/

@[expose] public section ScalarExtensionCoendCoherence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更した右 representable の相対 tensor 評価単位。 -/
def yonedaBaseChangeIso (z : D) (N : LeftModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D (representable A z)) (leftModule φ D N) ≅
      (extension φ).obj (N.obj z) :=
  (balancedIso φ D (representable A z) N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.yonedaIso A D z N)

@[reassoc (attr := simp)]
lemma ι_yonedaBaseChangeIso (z : D) (N : LeftModule A D) (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D (representable A z)) (leftModule φ D N) x ≫
      (yonedaBaseChangeIso φ D z N).hom =
      BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x z := by
  simp only [yonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, BalancedTensor.yonedaIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    BalancedTensor.ι_yonedaEvaluation, leftAction_comparison φ D N x z,
    Iso.inv_hom_id_assoc]

@[reassoc]
lemma yonedaBaseChange_comparison (z : D) (N : LeftModule A D) :
    (balancedIso φ D (representable A z) N).hom ≫ (yonedaBaseChangeIso φ D z N).hom =
      (extension φ).map (BalancedTensor.yonedaIso A D z N).hom := by
  simp only [yonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 係数変更した左 representable の相対 tensor 評価単位。 -/
def leftYonedaBaseChangeIso (z : D) (M : RightModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D (leftRepresentable A z)) ≅
      (extension φ).obj (M.obj (op z)) :=
  (balancedIso φ D M (leftRepresentable A z)).symm ≪≫
    (extension φ).mapIso (BalancedTensor.leftYonedaIso A D z M)

@[reassoc (attr := simp)]
lemma ι_leftYonedaBaseChangeIso (z : D) (M : RightModule A D) (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D (leftRepresentable A z)) x ≫
      (leftYonedaBaseChangeIso φ D z M).hom =
      BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) z x := by
  simp only [leftYonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, BalancedTensor.leftYonedaIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    BalancedTensor.ι_leftYonedaEvaluation, rightAction_comparison φ D M z x]
  change (tensorIso φ (M.obj (op x)) (homObject A D z x)).inv ≫
    (tensorIso φ (M.obj (op x)) (homObject A D z x)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

@[reassoc]
lemma leftYonedaBaseChange_comparison (z : D) (M : RightModule A D) :
    (balancedIso φ D M (leftRepresentable A z)).hom ≫
        (leftYonedaBaseChangeIso φ D z M).hom =
      (extension φ).map (BalancedTensor.leftYonedaIso A D z M).hom := by
  simp only [leftYonedaBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 複体パラメータを相対 tensor の外へ出す結合同型の係数変更。 -/
def tensorModuleBaseChangeIso (K : Complex A) (M : RightModule A D) (N : LeftModule A D) :
    BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D (tensorModule K M)) (leftModule φ D N) ≅
      (extension φ).obj K ⊗
        BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  (balancedIso φ D (tensorModule K M) N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.tensorModuleIso A D K M N) ≪≫
      tensorIso φ K (BalancedTensor.obj A D M N) ≪≫
        cochainTensorIso (Iso.refl _) (balancedIso φ D M N)

@[reassoc]
lemma ι_tensorModuleBaseChangeIso (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D)
        (rightModule φ D (tensorModule K M)) (leftModule φ D N) x ≫
      (tensorModuleBaseChangeIso φ D K M N).hom =
    (tensorIso φ K (M.obj (op x))).hom ▷ (extension φ).obj (N.obj x) ≫
      (α_ ((extension φ).obj K) ((extension φ).obj (M.obj (op x)))
        ((extension φ).obj (N.obj x))).hom ≫
      (extension φ).obj K ◁
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x := by
  simp only [tensorModuleBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, cochainTensorIso, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom,
    id_tensorHom, BalancedTensor.tensorModuleIso]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    BalancedTensor.ι_tensorModuleHom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := tensorIso_naturality φ (𝟙 K) (BalancedTensor.ι A D M N x)
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [← Category.assoc ((extension φ).map (K ◁ BalancedTensor.ι A D M N x))
    (tensorIso φ K (BalancedTensor.obj A D M N)).hom
    ((extension φ).obj K ◁ (balancedIso φ D M N).hom), hn]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, balancedIso_ι, whiskerLeft_comp]
  have ha := congrArg (fun f => (tensorIso φ (K ⊗ M.obj (op x)) (N.obj x)).inv ≫ f ≫
      (extension φ).obj K ◁
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x)
    (tensorIso_associator φ K (M.obj (op x)) (N.obj x)).symm
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at ha
  convert ha using 1

@[reassoc]
lemma tensorModuleBaseChange_comparison (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) :
    (balancedIso φ D (tensorModule K M) N).hom ≫
        (tensorModuleBaseChangeIso φ D K M N).hom =
      (extension φ).map (BalancedTensor.tensorModuleIso A D K M N).hom ≫
        (tensorIso φ K (BalancedTensor.obj A D M N)).hom ≫
          (extension φ).obj K ◁ (balancedIso φ D M N).hom := by
  simp only [tensorModuleBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, cochainTensorIso, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, id_tensorHom, Iso.hom_inv_id_assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionCoendCoherence
