module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies

/-!
概要：全ての指定形状の図式が余極限を持つとき、普遍余錐の射影は自明な Kan fibration。
方針：恒等図式に沿う既存の引き戻しの境界充填を、実引き戻しの同型で戻す。
規約：元の射影そのものの性質とし、余極限の追加の選択を要求しない。
使われ方：元の指定余極限全余錐間の全関手同型の構成。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 任意の元の図式の余極限存在から、普遍余錐の元の射影の全境界充填を得る。 -/
lemma colimitCoconeProjection_trivialKanFibration {K X : SSet.{u}} [Quasicategory X]
    (h : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd q (𝟙 ((ihom K).obj X))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection_pullback_trivialKanFibration (𝟙 _) (fun a =>
      h ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm a))
  let f := pullback.fst q (𝟙 ((ihom K).obj X))
  have : IsIso f := inferInstance
  have he : q = inv f ≫ pullback.snd q (𝟙 ((ihom K).obj X)) := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    simpa only [Category.comp_id] using (pullback.condition (f := q) (g := 𝟙 _))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q
  rw [he]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := pullback.snd q (𝟙 ((ihom K).obj X))))⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
