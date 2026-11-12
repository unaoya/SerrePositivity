module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardDiagram

/-!
# 元の混合二方向の二方向係数図式の augmentation

概要：元の全相対作用素と両端の表示を保って比較を図式に束ねる。
方針：元の切断関手の全自然性と底・両係数の関手則を使う。
規約：元の全圏・graph と同じ augmentation を保持する。
使われ方：DK10.3・5.7の元の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C) (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)

def forwardBackwardAugmentation : forwardBackwardDiagram D p hp w X Y ⟶
    (Functor.const I).obj (forwardBackwardData C w X Y) where
  app i := forwardBackwardDataMap w (A.app i) (ha i X) (ha i Y)
  naturality i j θ := by
    have hA : A.app i = D.map θ ≫ A.app j := by
      have he := (A.naturality θ).symm
      change A.app i ≫ 𝟙 C = D.map θ ≫ A.app j at he
      exact (Category.comp_id (A.app i : D.obj i ⟶ C)).symm.trans he
    change forwardBackwardDataMap w (D.map θ) (hp θ X) (hp θ Y) ≫
        forwardBackwardDataMap w (A.app j) (ha j X) (ha j Y) =
      forwardBackwardDataMap w (A.app i) (ha i X) (ha i Y) ≫ 𝟙 _
    rw [Category.comp_id]
    exact (forwardBackwardDataMap_comp w (D.map θ) (A.app j) (A.app i) hA
      (p i X) (p i Y) (p j X) (p j Y) X Y
      (hp θ X) (hp θ Y) (ha j X) (ha j Y) (ha i X) (ha i Y)).symm
end SerrePositivity.EInfinity.Hammock.FirstColumn
