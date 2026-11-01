module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGGraphCompositionInputLeft
public import SerrePositivity.KST.SConstruction.BimoduleRightUnitParameter

/-! # graph 合成比較の右入力に関する全次数自然性
概要：元の graph 合成比較は、右入力 dg 関手の任意 K 自然変換と可換。
方針：各元の対象で代表加群を回収し、実双加群の右単位のパラメータ自然性を使う。
規約：同じ合成比較と全次数 Hom を保持する。使われ方：入力横合成の実延長への移行。
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
  (F : DGFunctor A D E)

/-- graph で前合成した第一因子のパラメータ作用は、元の対象評価を厳密に回収する。 -/
lemma dgFunctorGraph_firstParam_evaluation {K : Complex A} {P P' : Bimodule A T E}
    (τ : BimoduleParamTrans A T E K P P') (d : D) :
    (BimoduleTensor.firstParam A T E D (functorGraph A D E F) τ).app d =
      (BimoduleTensor.firstParam A T E E (Bimodule.diagonal A E) τ).app (F.obj d) := by
  apply moduleHom_ext
  intro t
  change Bimodule.paramValue A T D
      (BimoduleTensor.firstParam A T E D (functorGraph A D E F) τ) t d =
    Bimodule.paramValue A T E
      (BimoduleTensor.firstParam A T E E (Bimodule.diagonal A E) τ) t (F.obj d)
  rw [BimoduleTensor.firstParam_value, BimoduleTensor.firstParam_value]
  rfl

/-- 任意 K の右入力変換は、元の graph 合成比較の前後で全次数に可換。 -/
lemma dgFunctorGraphComposition_input_right {K : Complex A} {G G' : DGFunctor A E T}
    (τ : DGFunctorParamTrans A E T K G G') (d : D) :
    (BimoduleTensor.firstParam A T E D (functorGraph A D E F)
        (dgFunctorGraphParameter A E T τ)).app d ≫
        moduleHomPostcompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G' d).hom =
      τ.app (F.obj d) ≫ yonedaHom A T (G.obj (F.obj d)) (G'.obj (F.obj d)) ≫
        moduleHomPrecompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G d).hom := by
  rw [← Category.assoc, ← dgFunctorGraphParameter_app]
  apply moduleHom_ext
  intro t
  simp only [Category.assoc]
  erw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [← Category.assoc]
  dsimp only [dgFunctorGraphCompositionAt, dgModuleExtensionRepresentableIso]
  erw [BimoduleTensor.rightUnitIso_hom_component, BimoduleTensor.rightUnitIso_hom_component]
  change Bimodule.paramValue A T D
      (BimoduleTensor.firstParam A T E D (functorGraph A D E F)
        (dgFunctorGraphParameter A E T τ)) t d ≫
        homPostcompose (BalancedTensor.obj A E (representable A (F.obj d))
          ((functorGraph A E T G).leftAt t))
          (BimoduleTensor.rightUnitValueIso A T E (functorGraph A E T G') t (F.obj d)).hom =
    Bimodule.paramValue A T E (dgFunctorGraphParameter A E T τ) t (F.obj d) ≫
      homPrecompose
        (BimoduleTensor.rightUnitValueIso A T E (functorGraph A E T G) t (F.obj d)).hom
        ((functorGraph A E T G').value t (F.obj d))
  rw [BimoduleTensor.firstParam_value]
  exact bimoduleRightUnitParameter_value A T E (dgFunctorGraphParameter A E T τ) t (F.obj d)

end SerrePositivity.KST.SConstruction
