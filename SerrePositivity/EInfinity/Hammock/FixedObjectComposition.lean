module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHammockMap
public import SerrePositivity.EInfinity.Hammock.RelativeFixedColimitMap

/-!
# 固定対象の hammock 図式の元の合成

概要：元の各次数の hammock 合成を全相対作用素に自然な合成に束ねる。
方針：元の図式の作用を固定端点の余極限写像へ照合する。
規約：元の全語の余極限・同じ端点表示・全単体を保持する。
使われ方：自由 hammock の対角の合成と左右比較の合成保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uI vI uO
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I : Type uI} [Category.{vI} I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  {O : Type uO} (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)

lemma hammockOperator_eq {i j : I} (θ : i ⟶ j) (X Y : O) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⋙ colim).map θ =
      Relative.fixedColimitMap (D.map θ) (hp θ X) (hp θ Y) := by
  apply congrArg colim.map
  apply NatTrans.ext
  funext w
  exact (Relative.fixedGraphDiagramMap_app (D.map θ) (hp θ X) (hp θ Y) w).symm

def hammockComposition (X Y Z : O) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⋙ colim) ⊗
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp Y Z).flip ⋙ colim) ⟶
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Z).flip ⋙ colim where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition (D.obj i).weakEquivalences (p i X) (p i Y) (p i Z)
  naturality i j θ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (D.obj j).weakEquivalences (p j X) (p j Y) (p j Z)
        ((((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⋙ colim).map θ).app n z.1)
        ((((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp Y Z).flip ⋙ colim).map θ).app n z.2) =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Z).flip ⋙ colim).map θ).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (D.obj i).weakEquivalences (p i X) (p i Y) (p i Z) z.1 z.2)
    rw [hammockOperator_eq, hammockOperator_eq, hammockOperator_eq]
    exact (Relative.fixedColimitMap_composePoint (D.map θ)
      (hp θ X) (hp θ Y) (hp θ Z) z.1 z.2).symm

end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
