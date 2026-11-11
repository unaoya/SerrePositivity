module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCoconeSurjective
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.JoinAssociatorRightPair
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IntervalTerminalSliceSection

/-!
概要：補間領域の始点余錐の頂点から、新しい終端頂点への全辺を計算する。
方針：全円柱比較の二座標を、結合同型の右二因子と標準区間で評価する。
規約：頂点だけでなく元の全辺を保持。使われ方：元の指定区間図式の帰還。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 補間領域の同じ始点余錐の右頂点を選ぶ実際の包含。 -/
def arrowInterpolationSourceTip (A : SSet.{u}) : (Δ[0] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ pushout.inr SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])

/-- この点は元の全円柱の同じ始点余錐の右頂点。 -/
lemma arrowInterpolationSourceTip_inclusion (A : SSet.{u}) :
    arrowInterpolationSourceTip A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
  rw [arrowInterpolationSourceTip, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_source]

/-- 二つの右頂点の全 join を折り畳むと、同じ元の余錐点へ送られる。 -/
lemma arrowInterpolationConeFold_rightPair (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u})) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold A =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinAssociator_rightPair, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]

/-- 元の始点余錐点から新終端点への全辺は、同じ余錐点と標準区間の二座標。 -/
lemma arrowInterpolationSourceTip_triangle (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A =
        lift (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom := by
  have hx : arrowInterpolationSourceTip A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) Δ[1] = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
    rw [← Category.assoc, arrowInterpolationSourceTip_inclusion, Category.assoc,
      SSet.ι₀_fst, Category.comp_id]
  have hy : arrowInterpolationSourceTip A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫
      snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) Δ[1] = stdSimplex.δ 1 := by
    rw [← Category.assoc, arrowInterpolationSourceTip_inclusion, Category.assoc,
      SSet.ι₀_snd, SSet.comp_const, stdSimplex.δ_one_eq_const]
  have hxm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫ fst _ _) (𝟙 Δ[0]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) (𝟙 Δ[0]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, hx]
  have hym : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫ snd _ _) (𝟙 Δ[0]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ 1) (𝟙 Δ[0]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, hy]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_fst]
    have h := (congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold A) hxm).trans
      (arrowInterpolationConeFold_rightPair A)
    simpa only [Category.assoc] using h
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_snd]
    have h := (congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1) hym).trans
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.intervalTerminalJoin_first
    simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
