module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
/-!
概要：固定図式の等式による slice の輸送の台を公開する。
方針：図式の等式を消去して恒等輸送に戻す。
規約：dg 圏・屋根・Small 仮定に依存しない。
使われ方：一般対象宇宙の slice prism の係数自然性と既存の屋根比較。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open CategoryTheory SSet
/-- 固定図式の等式による over slice の輸送は、台の join 射を変えない。 -/
lemma roofSliceTransport_val {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    {d : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).obj d) :
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom.app d s).val = s.val := by
  subst h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
