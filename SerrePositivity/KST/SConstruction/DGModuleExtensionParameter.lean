module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphParameter
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameters

/-! # 全パラメータの元の実 dg 加群延長への作用
概要：厳密 dg 入力間の K 自然変換を、実 graph 延長間の K 自然変換へ送る。
方針：実 graph 変換を相対 tensor の第一変数へ作用させる。
規約：全加群型の smallness や巨大な end を要求しない。使われ方：高次 Perf 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の実加群延長に対する、同じ K パラメータの全次数自然作用。 -/
def dgModuleExtensionParameter {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) :
    DGFunctorParamTrans A (RightModule A D) (RightModule A E) K
      (dgModuleExtension A D E F) (dgModuleExtension A D E G) :=
  BimoduleTensor.firstParam A E D (RightModule A D) (DGFunctor.id (RightModule A D))
    (dgFunctorGraphParameter A D E τ)

/-- 元の加群・対象での成分評価は、同じ graph 変換の実 tensor 作用。 -/
lemma dgModuleExtensionParameter_π {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (M : RightModule A D) (e : E) :
    (dgModuleExtensionParameter A D E τ).app M ≫
        moduleHomπ A E ((dgModuleExtension A D E F).obj M)
          ((dgModuleExtension A D E G).obj M) e =
      BimoduleTensor.firstParamHom A E D (RightModule A D) (DGFunctor.id (RightModule A D))
        (dgFunctorGraphParameter A D E τ) e M :=
  BimoduleTensor.firstParam_value A E D (RightModule A D) (DGFunctor.id (RightModule A D))
    (dgFunctorGraphParameter A D E τ) e M

end SerrePositivity.KST.SConstruction
