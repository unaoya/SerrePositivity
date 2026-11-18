module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnForwardBackwardDataCoherence

/-!
# 元の混合二方向の底と両係数の図式

概要：全相対作用素に沿う元の Data を図式へ束ねる。
方針：元の Data 写像全体の恒等・合成則を使う。
規約：元の固定対象表示を保持する。
使われ方：DK10.4–10.6の対角比較。
-/

@[expose] public section
noncomputable section
universe u v wO
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type wO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : O)
def forwardBackwardDiagram : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardData (D.obj i) w (p i X) (p i Y)
  map θ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w (D.map θ) (hp θ X) (hp θ Y)
  map_id i := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap_id w (D.map (𝟙 i)) (D.map_id i)
    (p i X) (p i Y) (hp (𝟙 i) X) (hp (𝟙 i) Y)
  map_comp {i j k} θ φ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap_comp w
    (D.map θ) (D.map φ) (D.map (θ ≫ φ)) (D.map_comp θ φ)
    (p i X) (p i Y) (p j X) (p j Y) (p k X) (p k Y)
    (hp θ X) (hp θ Y) (hp φ X) (hp φ Y) (hp (θ ≫ φ) X) (hp (θ ≫ φ) Y)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
