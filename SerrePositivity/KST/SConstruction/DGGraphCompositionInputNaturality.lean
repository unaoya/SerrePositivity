module
public import SerrePositivity.KST.SConstruction.DGGraphCompositionInputRight
public import SerrePositivity.KST.SConstruction.BimoduleSecondParameterHom
public import SerrePositivity.KST.SConstruction.DGFunctorHomPrecomposition

/-! # graph 合成比較と入力の二つの whiskering
概要：元の graph 合成比較は、入力の前合成・後合成の任意パラメータ作用と可換。
方針：実 tensor の第一・第二パラメータ作用を、左右の graph 比較自然性に接続する。
規約：元の graph 変換と全次数 Hom を保持する。使われ方：実延長の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [Small.{u} E] [DGCategory A T] [Small.{u} T]

/-- 入力の後合成と元の実 tensor の第二パラメータ作用は、graph 比較と全次数で可換。 -/
lemma dgFunctorGraphComposition_parameter_post {K : Complex A} {F F' : DGFunctor A D E}
    (G : DGFunctor A E T) (τ : DGFunctorParamTrans A D E K F F') (d : D) :
    (BimoduleTensor.secondParam A T E D (functorGraph A E T G)
        (dgFunctorGraphParameter A D E τ)).app d ≫
        moduleHomPostcompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F' G d).hom =
      (dgFunctorGraphParameter A D T (dgFunctorParamPost A D E T G τ)).app d ≫
        moduleHomPrecompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G d).hom := by
  rw [bimoduleSecondParam_postcomposition]
  have h := dgFunctorGraphComposition_input_left A E T G D τ d
  simp only [dgFunctorGraphParameter_app, dgFunctorParamPost, Category.assoc] at h ⊢
  convert h using 1 <;> rfl

/-- 入力の前合成と元の実 tensor の第一パラメータ作用は、graph 比較と全次数で可換。 -/
lemma dgFunctorGraphComposition_parameter_pre {K : Complex A} {G G' : DGFunctor A E T}
    (F : DGFunctor A D E) (τ : DGFunctorParamTrans A E T K G G') (d : D) :
    (BimoduleTensor.firstParam A T E D (functorGraph A D E F)
        (dgFunctorGraphParameter A E T τ)).app d ≫
        moduleHomPostcompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G' d).hom =
      (dgFunctorGraphParameter A D T (dgFunctorParamPre A E T D F τ)).app d ≫
        moduleHomPrecompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G d).hom := by
  have h := dgFunctorGraphComposition_input_right A D E T F τ d
  simp only [dgFunctorGraphParameter_app, dgFunctorParamPre, Category.assoc] at h ⊢
  convert h using 1
  rfl

end SerrePositivity.KST.SConstruction
