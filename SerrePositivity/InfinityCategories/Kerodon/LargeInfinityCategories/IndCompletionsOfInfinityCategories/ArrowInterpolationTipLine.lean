module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationTipTriangle

/-!
概要：全円柱同型の逆は、元の余錐頂点上の全区間を厳密に回収する。
方針：標準区間を二点の join として終端辺に写し、比較の二座標を計算する。
規約：同じ元の全辺を保持。使われ方：元の指定 Ind 射図式の回収。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の余錐頂点上の全区間を、補間領域の右余錐へ写す。 -/
def arrowInterpolationTipLine (A : SSet.{u}) : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) Δ[0] :=
  snd Δ[0] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationSourceTip A) (𝟙 Δ[0])

/-- 全区間の比較は、元の余錐頂点上の同じ全円柱包含。 -/
lemma arrowInterpolationTipLine_comp (A : SSet.{u}) :
    arrowInterpolationTipLine A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ▷ Δ[1] := by
  simp only [arrowInterpolationTipLine, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationSourceTip_triangle]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, whiskerRight_fst]
    have h : snd (Δ[0] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 = fst Δ[0] Δ[1] := stdSimplex.isTerminalObj₀.hom_ext _ _
    simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u})) h
  · simp only [Category.assoc, lift_snd, whiskerRight_snd, Iso.inv_hom_id, Category.comp_id]

/-- 元の余錐頂点上の全区間は、全円柱同型の逆で同じ終端辺に戻る。 -/
lemma arrowInterpolationCoconeIso_inv_tip (A : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso A).inv =
      arrowInterpolationTipLine A := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationTipLine_comp A).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
