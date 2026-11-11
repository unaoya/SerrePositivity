module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct

/-!
# 元の係数積の相対比較

概要：元の係数積と全相対作用素を保持する。
方針：両係数の元の写像と切断の全成分を組にする。
規約：同じ元の graph と augmentation を使う。
使われ方：DK10.3の混合二方向の自然な分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v v' w w'
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {B : Type v} [Category.{w} B] {B' : Type v'} [Category.{w'} B']
  {P Q : B ⥤ Cat.{u, u}} {P' Q' : B' ⥤ Cat.{u, u}}
  (F : B ⥤ B') (α : P ⟶ F ⋙ P') (β : Q ⟶ F ⋙ Q')
def change : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.diagram P Q ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.diagram P' Q' where
  app b := ((α.app b).toFunctor.prod (β.app b).toFunctor).toCatHom
  naturality b b' f := by
    apply Cat.Hom.ext
    change ((P.map f ≫ α.app b').toFunctor.prod (Q.map f ≫ β.app b').toFunctor) =
      ((α.app b ≫ P'.map (F.map f)).toFunctor.prod
        (β.app b ≫ Q'.map (F.map f)).toFunctor)
    rw [α.naturality, β.naturality]
    rfl
def pointMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point (B := B) ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point (B := B') where
  app b := 𝟙 _
  naturality _ _ _ := by rfl
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
