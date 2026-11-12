module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeDiagramLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionInitialReplacementPullback

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionReplaceInitial_comp_of_noninitial {A X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (a : A ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u})
    (ha : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured (nerveEquiv (a.app _ v))) :
    a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c = a ≫ F := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeDiagramLift_projection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured a ha]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_restrict, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
