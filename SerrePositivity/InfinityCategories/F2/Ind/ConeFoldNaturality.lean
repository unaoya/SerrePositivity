module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCocone
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint

/-!
概要：二重余錐の折り畳みは元の形状に自然で、右二点を潰す区間表示を保持する。
方針：join 結合同型の全自然性と標準二単体の有限計算を使う。
規約：全次数の射の等式。使われ方：終端辺を固定した標準持ち上げの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の形状の全射は、二重余錐の同じ右二点の折り畳みと可換。 -/
lemma arrowInterpolationConeFold_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    joinMap (joinMap f (𝟙 (Δ[0] : SSet.{u}))) (𝟙 Δ[0]) ≫ arrowInterpolationConeFold B =
      arrowInterpolationConeFold A ≫ joinMap f (𝟙 Δ[0]) := by
  rw [arrowInterpolationConeFold, arrowInterpolationConeFold, ← Category.assoc,
    stableJoinAssociator_naturality, Category.assoc, ← joinMap_comp,
    Category.assoc, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id, joinMap_id]

/-- 二重点余錐の折り畳みは、同じ区間の右二点の潰しに一致する。 -/
lemma arrowInterpolationConeFold_interval :
    arrowInterpolationConeFold (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso 0 0).hom =
      joinMap (joinStdSimplexIso 0 0).hom (𝟙 Δ[0]) ≫ stableLastJoinEvaluation 1 := by
  let e := joinIso (joinStdSimplexIso.{u} 0 0) (Iso.refl (Δ[0] : SSet.{u})) ≪≫
    joinStdSimplexIso 1 0
  apply (cancel_epi e.inv).mp
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.F2.Ind
