module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TrivialCosliceEndpointLifting

/-!
概要：自明 Kan 射に沿う相対 coslice の射は自明 Kan。
方針：元の図式・余錐・余錐頂点を join の部分複体で貼り合わせ、その単射を持ち上げる。
規約：始域と底の quasicategory 性や形状の有限性を要求しない。
使われ方：Ind 模型での全前置図式の因子化を元の accessible 圏へ厳密に戻す。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の余錐と頂点の全境界は、自明 Kan 射に沿って同時に持ち上がる。
方針：部分余錐と全頂点族を pushout-join 上で貼り、その単射を持ち上げる。
規約：部分境界には anodyne 性や同値性を要求しない。
使われ方：相対 coslice の全境界持ち上げ。 -/
lemma cosliceEndpointMap_lift_of_trivialKan {A K E B : SSet.{u}}
    (a : K ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.cosliceEndpointMap_lifting_of_trivial a p A₀

/-- 概要：自明 Kan 射の元の相対 coslice も自明 Kan 射。
方針：全境界の同時持ち上げを境界判定へ渡す。
規約：元の全図式と余錐の指定辺を保持する。
使われ方：両端点と底の脚を固定した全余錐因子化の移送。 -/
lemma cosliceEndpointMap_trivialKanFibration {K E B : SSet.{u}}
    (a : K ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
    (fun n ↦ cosliceEndpointMap_lift_of_trivialKan a p (boundary n))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
