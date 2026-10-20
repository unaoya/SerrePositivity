module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHom
public import SerrePositivity.KST.SConstruction.LeftTensorHomComposition

/-! # 元の実加群延長の入力 Hom の単位・合成保存
概要：元の入力 Hom の作用は、各実加群で全次数の単位と合成を保持する。
方針：全対象評価で、graph の左加群 Hom の作用と実 tensor dg 関手へ帰着する。
規約：実加群全体の end を要求しない。使われ方：Perf とラベル付き高次作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の入力 Hom の閉単位は、各実加群延長の同じ閉単位へ送られる。 -/
lemma dgModuleExtensionInputHom_identity (F : DGFunctor A D E) (M : RightModule A D) :
    dgFunctorIdentity A D E F ≫ dgModuleExtensionInputHom A D E F F M =
      moduleIdentity A E ((dgModuleExtension A D E F).obj M) := by
  apply moduleHom_ext
  intro e
  rw [Category.assoc, dgModuleExtensionInputHom_π, ← Category.assoc,
    dgFunctorGraphLeftHom_identity, moduleIdentity_π]
  exact (BalancedTensor.leftTensorDG A D M).map_id ((functorGraph A D E F).leftAt e)

/-- 元の入力 Hom の全次数合成は、各実加群延長の同じ合成へ送られる。 -/
lemma dgModuleExtensionInputHom_composition (F G H : DGFunctor A D E) (M : RightModule A D) :
    dgFunctorComposition A D E F G H ≫ dgModuleExtensionInputHom A D E F H M =
      (dgModuleExtensionInputHom A D E F G M ⊗ₘ dgModuleExtensionInputHom A D E G H M) ≫
        moduleComposition A E ((dgModuleExtension A D E F).obj M)
          ((dgModuleExtension A D E G).obj M) ((dgModuleExtension A D E H).obj M) := by
  apply moduleHom_ext
  intro e
  simp only [Category.assoc, moduleComposition_π, tensorHom_comp_tensorHom_assoc,
    dgModuleExtensionInputHom_π, dgModuleExtension_value]
  have h := congrArg (fun k => k ≫ BalancedTensor.leftHomMap A D M
    ((functorGraph A D E F).leftAt e) ((functorGraph A D E H).leftAt e))
      (dgFunctorGraphLeftHom_composition A D E F G H e)
  have hc := congrArg (fun k =>
    (dgFunctorGraphLeftHom A D E F G e ⊗ₘ dgFunctorGraphLeftHom A D E G H e) ≫ k)
      (dgLeftTensorHom_composition A D M ((functorGraph A D E F).leftAt e)
        ((functorGraph A D E G).leftAt e) ((functorGraph A D E H).leftAt e))
  simp only [Category.assoc] at h hc
  rw [tensorHom_comp_tensorHom_assoc] at hc
  rw [h]
  exact hc

end SerrePositivity.KST.SConstruction
