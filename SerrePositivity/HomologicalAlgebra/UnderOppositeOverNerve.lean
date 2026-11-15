module
public import SerrePositivity.HomologicalAlgebra.UnderNerveWeight
public import Mathlib.CategoryTheory.Category.Cat.Op
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan

/-!
概要：反対圏の under nerve 重みを、over nerve 重みの単体的順序反転と比較する。
方針：Under(op j) と (Over j)ᵒᵖ の厳密な逆関手、既存の nerve 反転同型を合成する。
規約：圏の反対化と単体集合の反転を区別する。重みの底の全射に自然。
使われ方：HA 1.2.4、G10 の線形 bar 重みと BK の共変 over 重みの向きの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type) [SmallCategory J]

/-- 構造射を反対にする厳密な逆関手は、同じ under と over の nerve の同型を与える。 -/
def underOppositeOverNerveIso (j : J) : nerve (Under (op j)) ≅ nerve (Over j)ᵒᵖ where
  hom := nerveMap (Under.opEquivOpOver j).functor
  inv := nerveMap (Under.opEquivOpOver j).inverse
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 底の二重反対圏を戻した under 重みは、over 圏を反対にしてから nerve を取った重み。 -/
def underOppositeOverWeightIso :
    (opOpEquivalence J).inverse ⋙ underNerveWeight Jᵒᵖ ≅
      Over.mapFunctor J ⋙ Cat.opFunctor ⋙ nerveFunctor :=
  NatIso.ofComponents (underOppositeOverNerveIso J) (by
    intro i j f
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.hext ?_ ?_
    · intro k
      rfl
    · intro k l h
      rfl)

/-- 反対 under の重みは BK の over 重みの単体的順序反転と自然同型。 -/
def underOppositeBousfieldKanWeightIso :
    (opOpEquivalence J).inverse ⋙ underNerveWeight Jᵒᵖ ≅
      SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight J ⋙
        SSet.opFunctor :=
  underOppositeOverWeightIso J ≪≫
    (NatIso.ofComponents
      (fun j => SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := Over j))
      (by
        intro i j f
        exact SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeMap_naturality
          (Over.map f))).symm

end SerrePositivity.HomologicalAlgebra
