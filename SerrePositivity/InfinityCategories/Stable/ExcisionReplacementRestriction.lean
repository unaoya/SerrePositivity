module
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeDiagramLift
public import SerrePositivity.InfinityCategories.Stable.ExcisionInitialReplacementPullback

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
namespace SerrePositivity.InfinityCategories

lemma excisionReplaceInitial_comp_of_noninitial {A X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (a : A ⟶ nerve ExcisionGridIndex.{u})
    (ha : ∀ v : A _⦋0⦌, IsExcisionFullPunctured (nerveEquiv (a.app _ v))) :
    a ≫ excisionReplaceInitial c = a ≫ F := by
  rw [← posetSubtypeDiagramLift_projection IsExcisionFullPunctured a ha]
  rw [Category.assoc, excisionReplaceInitial_restrict, Category.assoc]

end SerrePositivity.InfinityCategories
