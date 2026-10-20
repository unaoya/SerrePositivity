module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter
public import SerrePositivity.KST.SConstruction.BimoduleSecondParameterHom

/-! # 元の実加群延長の二つの入力作用の tensor 表示
概要：入力の前後合成に現れる作用を、同じ実 tensor の第一・第二作用として回収する。
方針：右端の対象評価を保ち、元の全 Hom の後合成との一致を使う。
規約：全加群型の smallness は要求しない。使われ方：入力の合成比較の全次数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded

/-- 第一 tensor 因子のパラメータ作用は、後因子の元の右加群値だけで決まる。 -/
lemma bimoduleFirstParam_evaluation (A : Type u) [CommRing A] (B : Type v) (C : Type w)
    (E : Type z) [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
    [DGCategory A E] {K : Complex A} {P P' : Bimodule A B C}
    (Q : Bimodule A C E) (τ : BimoduleParamTrans A B C K P P') (e : E) :
    (BimoduleTensor.firstParam A B C E Q τ).app e =
      (BimoduleTensor.firstParam A B C (RightModule A C) (DGFunctor.id _) τ).app
        (Q.rightAt e) := by
  apply moduleHom_ext
  intro b
  change Bimodule.paramValue A B E (BimoduleTensor.firstParam A B C E Q τ) b e =
    Bimodule.paramValue A B (RightModule A C)
      (BimoduleTensor.firstParam A B C (RightModule A C) (DGFunctor.id _) τ) b (Q.rightAt e)
  rw [BimoduleTensor.firstParam_value, BimoduleTensor.firstParam_value]
  rfl

variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 左入力の実延長作用をさらに延長することは、元の第二 tensor 作用。 -/
lemma dgModuleExtensionParameter_post_action {K : Complex A} {F F' : DGFunctor A D E}
    (G : DGFunctor A E T) (τ : DGFunctorParamTrans A D E K F F') (M : RightModule A D) :
    (BimoduleTensor.secondParam A T E (RightModule A D) (functorGraph A E T G)
        (dgModuleExtensionParameter A D E τ)).app M =
      (dgModuleExtensionParameter A D E τ).app M ≫ (dgModuleExtension A E T G).map
        ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F').obj M) :=
  bimoduleSecondParam_postcomposition A T E (RightModule A D) (functorGraph A E T G)
    (dgModuleExtensionParameter A D E τ) M

/-- 右入力の実延長作用の元の加群での評価は、同じ第一 tensor 作用。 -/
lemma dgModuleExtensionParameter_pre_action {K : Complex A} {G G' : DGFunctor A E T}
    (F : DGFunctor A D E) (τ : DGFunctorParamTrans A E T K G G') (M : RightModule A D) :
    (BimoduleTensor.firstParam A T E (RightModule A D) (dgModuleExtension A D E F)
        (dgFunctorGraphParameter A E T τ)).app M =
      (dgModuleExtensionParameter A E T τ).app ((dgModuleExtension A D E F).obj M) :=
  bimoduleFirstParam_evaluation A T E (RightModule A D) (dgModuleExtension A D E F)
    (dgFunctorGraphParameter A E T τ) M

end SerrePositivity.KST.SConstruction
