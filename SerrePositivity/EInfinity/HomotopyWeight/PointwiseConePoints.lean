module

public import SerrePositivity.EInfinity.HomotopyWeight.ConePoints
public import SerrePositivity.EInfinity.HomotopyWeight.PointwiseTensorFrame

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

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)

/-- 概要：各値の実現の射から作る零単体は同じ図式 frame Hom の像（Hovey §5.4）。
方針：合成随伴を展開し、各値の実現随伴の始域自然性を使う。
規約：元の零次同型と元の射を使う。
使われ方：元の定値図式比較の錐の類の照合。 -/
lemma pointwiseTensorFrameHomIso_point {F : K ⥤ C}
    (f : (pointwiseRealization K B).obj W ⟶ F) :
    ((((pointwiseTensorFrameHomIso K W B).app F).hom).app (Opposite.op (SimplexCategory.mk 0)))
        ((pointwiseTensorFrameZeroIso K W B).hom ≫ f) =
      conePoint K W ((pointwiseRealizationAdjunction K B).homEquiv W F f) := by
  change SSet.yonedaEquiv ((pointwiseTensorAdjunction K W B).homEquiv _ F (_ ≫ f)) =
    SSet.yonedaEquiv ((WeightedCones.adjunction K W).homEquiv _ _
      ((zeroTensorWeightIso K W).hom ≫
        (pointwiseRealizationAdjunction K B).homEquiv W F f))
  simp only [pointwiseTensorAdjunction, Adjunction.comp_homEquiv]
  exact congrArg (fun h => SSet.yonedaEquiv ((WeightedCones.adjunction K W).homEquiv _ _ h))
    ((pointwiseRealizationAdjunction K B).homEquiv_naturality_left _ f)

end SerrePositivity.EInfinity.HomotopyWeight
