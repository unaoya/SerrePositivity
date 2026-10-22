module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeSurjective
public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorRightPair
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalTerminalSliceSection

/-!
概要：補間領域の始点余錐の頂点から、新しい終端頂点への全辺を計算する。
方針：全円柱比較の二座標を、結合同型の右二因子と標準区間で評価する。
規約：頂点だけでなく元の全辺を保持。使われ方：元の指定区間図式の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 補間領域の同じ始点余錐の右頂点を選ぶ実際の包含。 -/
def arrowInterpolationSourceTip (A : SSet.{u}) : (Δ[0] : SSet.{u}) ⟶
    arrowInterpolationCorner A := joinInr A Δ[0] ≫ pushout.inr SSet.ι₀ (joinInl A Δ[0])

/-- この点は元の全円柱の同じ始点余錐の右頂点。 -/
lemma arrowInterpolationSourceTip_inclusion (A : SSet.{u}) :
    arrowInterpolationSourceTip A ≫ arrowInterpolationCornerInclusion A =
      joinInr A (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
  rw [arrowInterpolationSourceTip, Category.assoc, arrowInterpolationCornerInclusion_source]

/-- 二つの右頂点の全 join を折り畳むと、同じ元の余錐点へ送られる。 -/
lemma arrowInterpolationConeFold_rightPair (A : SSet.{u}) :
    joinMap (joinInr A (Δ[0] : SSet.{u})) (𝟙 Δ[0]) ≫ arrowInterpolationConeFold A =
      stableLastJoinEvaluation 0 ≫ joinInr A Δ[0] := by
  rw [arrowInterpolationConeFold, ← Category.assoc, joinAssociator_rightPair, joinInr_joinMap]

/-- 元の始点余錐点から新終端点への全辺は、同じ余錐点と標準区間の二座標。 -/
lemma arrowInterpolationSourceTip_triangle (A : SSet.{u}) :
    joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      arrowInterpolationCocone A =
        lift (stableLastJoinEvaluation 0 ≫ joinInr A Δ[0]) (joinStdSimplexIso 0 0).hom := by
  have hx : arrowInterpolationSourceTip A ≫ arrowInterpolationCornerInclusion A ≫
      fst (join A (Δ[0] : SSet.{u})) Δ[1] = joinInr A Δ[0] := by
    rw [← Category.assoc, arrowInterpolationSourceTip_inclusion, Category.assoc,
      SSet.ι₀_fst, Category.comp_id]
  have hy : arrowInterpolationSourceTip A ≫ arrowInterpolationCornerInclusion A ≫
      snd (join A (Δ[0] : SSet.{u})) Δ[1] = stdSimplex.δ 1 := by
    rw [← Category.assoc, arrowInterpolationSourceTip_inclusion, Category.assoc,
      SSet.ι₀_snd, SSet.comp_const, stdSimplex.δ_one_eq_const]
  have hxm : joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      joinMap (arrowInterpolationCornerInclusion A ≫ fst _ _) (𝟙 Δ[0]) =
        joinMap (joinInr A Δ[0]) (𝟙 Δ[0]) := by
    rw [← joinMap_comp, Category.id_comp, hx]
  have hym : joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u})) ≫
      joinMap (arrowInterpolationCornerInclusion A ≫ snd _ _) (𝟙 Δ[0]) =
        joinMap (stdSimplex.δ 1) (𝟙 Δ[0]) := by
    rw [← joinMap_comp, Category.id_comp, hy]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [arrowInterpolationCocone, Category.assoc, lift_fst]
    have h := (congrArg (fun f => f ≫ arrowInterpolationConeFold A) hxm).trans
      (arrowInterpolationConeFold_rightPair A)
    simpa only [Category.assoc] using h
  · simp only [arrowInterpolationCocone, Category.assoc, lift_snd]
    have h := (congrArg (fun f => f ≫ stableLastJoinEvaluation 1) hym).trans
      intervalTerminalJoin_first
    simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Ind
