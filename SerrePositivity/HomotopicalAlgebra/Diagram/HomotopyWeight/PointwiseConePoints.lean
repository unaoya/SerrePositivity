module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorFrame

/-!
# 各値の実現随伴から作った錐の零単体

概要：Hovey §5.4 の図式 frame の零次の Hom と元の錐の零単体を照合する。
方針：同じ零単体テンソル同型を二つの随伴の自然性で追跡する。
規約：元の図式・重み・係数 frame を保持する。
使われ方：通常の錐の始域 frame の類の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)

/-- 概要：各値の実現の射から作る零単体は同じ図式 frame Hom の像（Hovey §5.4）。
方針：合成随伴を展開し、各値の実現随伴の始域自然性を使う。
規約：元の零次同型と元の射を使う。
使われ方：元の定値図式比較の錐の類の照合。 -/
lemma pointwiseTensorFrameHomIso_point {F : K ⥤ C}
    (f : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).obj W ⟶ F) :
    ((((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K W B).app F).hom).app (Opposite.op (SimplexCategory.mk 0)))
        ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K W B).hom ≫ f) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint K W ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K B).homEquiv W F f) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorAdjunction K W B).homEquiv _ F (_ ≫ f)) =
    SSet.yonedaEquiv ((WeightedCones.adjunction K W).homEquiv _ _
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K W).hom ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K B).homEquiv W F f))
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorAdjunction, Adjunction.comp_homEquiv]
  exact congrArg (fun h => SSet.yonedaEquiv ((WeightedCones.adjunction K W).homEquiv _ _ h))
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K B).homEquiv_naturality_left _ f)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
