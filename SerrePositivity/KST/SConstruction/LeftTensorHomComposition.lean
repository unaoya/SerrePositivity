module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-! # 元の実左 tensor Hom 写像の全次数合成
概要：既存の左 tensor dg 関手の合成法則を、元の Hom 写像で明示する。
方針：抽象左加群で既存の dg 関手の法則を適用する。
規約：元の coend・合成写像を変更しない。使われ方：graph 代入後の実延長の合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の実左 tensor Hom 写像は、既存の左加群 Hom の全次数合成を保持する。 -/
lemma dgLeftTensorHom_composition (M : RightModule A D) (N N' P : LeftModule A D) :
    moduleComposition A Dᵒᵖ N.toRightOpposite N'.toRightOpposite P.toRightOpposite ≫
        BalancedTensor.leftHomMap A D M N P =
      (BalancedTensor.leftHomMap A D M N N' ⊗ₘ BalancedTensor.leftHomMap A D M N' P) ≫
        enrichedComposition (BalancedTensor.obj A D M N) (BalancedTensor.obj A D M N')
          (BalancedTensor.obj A D M P) :=
  (BalancedTensor.leftTensorDG A D M).map_comp N N' P

end SerrePositivity.KST.SConstruction
