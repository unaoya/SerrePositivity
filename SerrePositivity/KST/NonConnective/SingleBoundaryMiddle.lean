module

public import SerrePositivity.KST.NonConnective.AdditivityGroupDecomposition
public import SerrePositivity.KST.NonConnective.CofiberAxes

/-!
概要：同じ一重 S• 境界商 Kan 模型の群における中央項の加法性。
方針：元の加法性の射対の単射性と、実標準軸の六つの評価で群を分解する。
規約：中央項の加法公式を仮定しない。使われ方：固定 K の swindle。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 一重境界商 Kan 模型の元の完全射による正次数群準同型。 -/
def singleBoundaryGroupMap {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pointedGroupMap n ((boundaryKanRealizationFunctor 0).map f)

/-- 同じ元の群作用の恒等法則。 -/
lemma singleBoundaryGroupMap_id (X : StableModel.{u}) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj X).right n
      ((boundaryKanRealizationFunctor 0).obj X).basepoint) :
    singleBoundaryGroupMap (𝟙 X) n a = a := by
  unfold singleBoundaryGroupMap
  rw [CategoryTheory.Functor.map_id]
  exact pointedGroupMap_id _ _ _

/-- 同じ元の群作用の合成法則。 -/
lemma singleBoundaryGroupMap_comp {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj X).right n
      ((boundaryKanRealizationFunctor 0).obj X).basepoint) :
    singleBoundaryGroupMap (f ≫ g) n a =
      singleBoundaryGroupMap g n (singleBoundaryGroupMap f n a) := by
  unfold singleBoundaryGroupMap
  rw [CategoryTheory.Functor.map_comp, pointedGroupMap_comp]

/-- 元の中央項の群作用は、同じ subobject・quotient の群作用の積である。 -/
theorem singleBoundaryMiddle_additivity (X : StableModel.{u}) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj
      (cofiberStableModel X)).right n
      ((boundaryKanRealizationFunctor 0).obj (cofiberStableModel X)).basepoint) :
    singleBoundaryGroupMap (cofiberStableMiddle X) n a =
      singleBoundaryGroupMap (cofiberStableSubobject X) n a *
        singleBoundaryGroupMap (cofiberStableQuotient X) n a := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier
  apply additivityGroup_middle
    (singleBoundaryGroupMap (cofiberStableSubobject X) n)
    (singleBoundaryGroupMap (cofiberStableQuotient X) n)
    (singleBoundaryGroupMap (cofiberStableMiddle X) n)
    (singleBoundaryGroupMap (zeroCofiberStableFunctor X z false) n)
    (singleBoundaryGroupMap (zeroCofiberStableFunctor X z true) n)
    (boundaryKanAdditivityGroup_injective 0 X n)
  · intro x
    rw [← singleBoundaryGroupMap_comp, cofiberAxisLeft_subobject,
      singleBoundaryGroupMap_id]
  · intro x
    rw [← singleBoundaryGroupMap_comp, cofiberAxisLeft_quotient]
    exact singleBoundaryKanGroup_constantZero X z n x
  · intro x
    rw [← singleBoundaryGroupMap_comp, zeroCofiberStableFunctor_subobject_true]
    exact singleBoundaryKanGroup_constantZero X z n x
  · intro x
    rw [← singleBoundaryGroupMap_comp, zeroCofiberStableFunctor_quotient,
      singleBoundaryGroupMap_id]
  · intro x
    rw [← singleBoundaryGroupMap_comp, cofiberAxes_middle, singleBoundaryGroupMap_id]
  · intro x
    rw [← singleBoundaryGroupMap_comp, cofiberAxes_middle, singleBoundaryGroupMap_id]

end SerrePositivity.KST.NonConnective
