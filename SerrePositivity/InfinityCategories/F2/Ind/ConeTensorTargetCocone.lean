module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorTargetInclusion
public import SerrePositivity.InfinityCategories.F2.Ind.ConeFoldApexConstant
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeIso
public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorOuterPair

/-!
概要：元の補間領域の終点包含の余錐は、同じ余錐積比較で元の全終点面を回収する。
方針：元の二座標の折り畳みと、元の余錐点での定値性を照合する。
規約：元の全族と同じ全余錐面を厳密に保持する。
使われ方：指定評価下の相対余錐を、元の全終点拡張へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の終点包含への全余錐は、元の余錐積比較の同じ全終点面。
方針：元の二射影を照合。規約：全射の等号。使われ方：指定変換の全拡張への移送。 -/
lemma coneTensorCocone_target (A L : SSet.{u}) :
    joinMap (coneTensorTargetInclusion A L) (𝟙 (Δ[0] : SSet.{u})) ≫
      coneTensorCocone A L = tensorRightPoint (join A Δ[0]) (joinInr L Δ[0]) := by
  have hF : coneTensorTargetInclusion A L ≫ coneTensorCornerInclusion A L ≫
      fst (join A (Δ[0] : SSet.{u})) (join L Δ[0]) = joinInl A Δ[0] := by
    rw [← Category.assoc, coneTensorTargetInclusion_comp, Category.assoc,
      tensorRightPoint_fst, Category.comp_id]
  have hS : coneTensorTargetInclusion A L ≫ coneTensorCornerInclusion A L ≫
      snd (join A (Δ[0] : SSet.{u})) (join L Δ[0]) =
      SSet.const (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u}))) := by
    rw [← Category.assoc, coneTensorTargetInclusion_comp, Category.assoc,
      tensorRightPoint_snd, SSet.comp_const]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [coneTensorCocone, Category.assoc, lift_fst, tensorRightPoint_fst]
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, hF,
      arrowInterpolationConeFold_outerPair]
  · simp only [coneTensorCocone, Category.assoc, lift_snd, tensorRightPoint_snd]
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id, hS,
      arrowInterpolationConeFold_apex_constant]
/-- 概要：元の全余錐積の逆比較も、同じ元の全終点面を厳密に回収する。
方針：元の比較同型を相殺。規約：全射の等号。使われ方：指定変換の全拡張への帰還。 -/
lemma coneTensorCoconeIso_inv_target (A L : SSet.{u}) :
    tensorRightPoint (join A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫
      (coneTensorCoconeIso A L).inv =
    joinMap (coneTensorTargetInclusion A L) (𝟙 (Δ[0] : SSet.{u})) := by
  apply (cancel_mono (coneTensorCoconeIso A L).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (coneTensorCocone_target A L).symm
end SerrePositivity.InfinityCategories.F2.Ind
