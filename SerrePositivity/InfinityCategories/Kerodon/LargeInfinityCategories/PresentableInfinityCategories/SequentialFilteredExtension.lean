module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveStageModel

/-!
概要：filtered 圏への有限始区間の図式を次の始区間へ厳密に延長する。
方針：始区間を標準単体と同定し、その余錐を次元が一つ大きい標準単体へ輸送する。
規約：元の全図式との一致を射の等式として保持する。
使われ方：引き戻しの交互構成の有限段階の延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：filtered 圏への有限始区間の全図式は次の始区間へ延長できる。
方針：標準単体上の元の図式の余錐を join 表示で貼る。
規約：指定された図式を前段階への制限で厳密に回収する。
使われ方：整合する可算図式の有限段階を選ぶ。 -/
lemma exists_sequentialNerveStage_extension {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity X] (n : ℕ) (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ⟶ X) :
    ∃ g : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} (n + 1) : SSet.{u}) ⟶ X,
      Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n)) ≫ g = f := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso.{u} n
  let e' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso.{u} (n + 1)
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty (e.inv ≫ f)
  refine ⟨e'.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ c.val, ?_⟩
  rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso_transition]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl n |>.symm]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, c.property]
  exact e.hom_inv_id_assoc f

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
