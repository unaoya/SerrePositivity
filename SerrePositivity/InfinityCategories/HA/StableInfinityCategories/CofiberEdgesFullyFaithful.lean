module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableClosureFullyFaithful
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingBaseChange

/-! # 完全充満忠実関手による実 cofiber 分母の反映

概要：実分母の所属は完全充満忠実関手で保存・反映される。
方針：指定辺の実 cofiber を完全関手で写し、その頂点の実閉包条件を反映する。
規約：辺と cofiber の選択を厳密に保持。使われ方：実 Yoneda からの分母の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]

/-- 完全充満忠実関手は、指定頂点の実閉包で定まる cofiber 分母の所属を反映する。 -/
theorem cofiberStableEdges_map_iff (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F) (P : Set (X _⦋0⦌)) {x y : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (f.map ((truncation 2).map F)).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (F.app (Opposite.op ⦋0⦌) '' P) z} ↔
      f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff _ (s.map F)).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff F hf P s.cofiber).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff P s).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
