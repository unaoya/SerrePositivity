module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws

/-! # 任意kernelの通常作用の余極限保存

## 概要
右E・左D kernelの通常tensor作用がu-small図式の余極限を保存することを証明する。

## 方針
出力評価を既存のbalanced tensor左随伴へ比較し、加群の評価による余極限反映を使う。

## 規約と注意
係数は任意可換環。kernelの射影性・局所Hom K-flat性は要求しない。
添字の対象はSmall.{u}で、射の宇宙は独立。

## 使われ方
U16aの主導来kernel作用の余積保存と一般右随伴の表現対象構成に使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  {J : Type z} [Category.{z'} J] [Small.{u} J]

/-- 評価とbalanced tensorとの比較から、通常kernel作用が余極限coconeを保存する。 -/
def kernelTensorIsColimit {F : J ⥤ ModuleCategory A D} (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((kernelTensor A D E P).onClosed.mapCocone c) := by
  apply moduleIsColimitOfEvaluations A E
  intro e
  let : PreservesColimit F ((kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E e) :=
    preservesColimit_of_natIso F (perfectKernelTensorEvaluationIso A D E P e).symm
  exact isColimitOfPreserves ((kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E e) hc

/-- 任意kernelの通常作用は、対象添字がu-smallな図式の余極限を保存する。 -/
instance kernelTensorPreservesColimitsOfShape :
    PreservesColimitsOfShape J (kernelTensor A D E P).onClosed where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
      (kernelTensorIsColimit A D E P (colimit.cocone F) (colimit.isColimit F))

end SerrePositivity.DifferentialGraded.Morita
