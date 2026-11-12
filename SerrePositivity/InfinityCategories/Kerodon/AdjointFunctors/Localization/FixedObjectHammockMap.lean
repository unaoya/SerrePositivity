module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialColimit

/-!
# 固定対象の hammock 図式の係数写像

概要：元の係数自然変換を全語の余極限と対角へ移す。
方針：同じ余極限包含の可換式を全次数で使う。
規約：元の全語・全単体作用素を保持する。
使われ方：自由 hammock の左右比較の係数自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
universe u uI vI uO uP
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits
variable {I : Type uI} [Category.{vI} I] (D E : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  {O : Type uO} {P : Type uP}
  (p : (i : I) → O → (D.obj i).category) (q : (i : I) → P → (E.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (hq : ∀ {i j : I} (θ : i ⟶ j) (X : P), (E.map θ).functor.obj (q i X) = q j X)
  (A : D ⟶ E) (s : O → P) (hA : ∀ i X, (A.app i).functor.obj (p i X) = q i (s X))

def hammockMap (X Y : O) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⋙ colim ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram E q hq (s X) (s Y)).flip ⋙ colim :=
  Functor.whiskerRight
    ((flipFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word I SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryMap.graphWordMap D E p q hp hq A s hA X Y)) colim

lemma hammockMap_inclusion (X Y : O) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryMap.graphWordMap D E p q hp hq A s hA X Y).app w ≫
        (pointwiseCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram E q hq (s X) (s Y))).ι.app w =
      (pointwiseCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y)).ι.app w ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.hammockMap D E p q hp hq A s hA X Y := by
  apply NatTrans.ext
  funext i
  exact (colimit.ι_map
    (((flipFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word I SSet.{u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryMap.graphWordMap D E p q hp hq A s hA X Y)).app i) w).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
