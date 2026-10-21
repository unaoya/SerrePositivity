module

public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：一点図式の元の錐から恒等錐への比較三角形の形状を固定する。
方針：最後の頂点を重ねる退化写像の四つの制限を照合する。
規約：新たな辺を選ばない。使われ方：一点の極限錐と指定脚の可逆性の同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の脚の終点を重ねる比較三角形の形状写像。 -/
def pointConeDegeneracy : join (Δ[1] : SSet.{u}) Δ[0] ⟶ join (Δ[0] : SSet.{u}) Δ[0] :=
  (joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ (joinStdSimplexIso 0 0).inv

/-- 比較三角形の固定された終点は元の終点。 -/
lemma pointConeDegeneracy_inr :
    joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ pointConeDegeneracy = joinInr Δ[0] Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).1
  simp only [pointConeDegeneracy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  decide

/-- 比較三角形の始点側の面は元の脚。 -/
lemma pointConeDegeneracy_face_one :
    joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫
      pointConeDegeneracy = 𝟙 _ := by
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).1
  apply (cancel_epi (joinStdSimplexIso 0 0).inv).1
  simp only [pointConeDegeneracy, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.id_comp]
  apply SSet.yonedaEquiv.injective
  decide

/-- 比較三角形の終点側の面は元の終点で定値。 -/
lemma pointConeDegeneracy_face_zero :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫ pointConeDegeneracy =
      SSet.const (SSet.yonedaEquiv (joinInr (Δ[0] : SSet.{u}) Δ[0])) := by
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).1
  apply (cancel_epi (joinStdSimplexIso 0 0).inv).1
  simp only [pointConeDegeneracy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  decide

/-- 比較三角形の底にある辺は元の脚を表す標準辺。 -/
lemma pointConeDegeneracy_inl :
    joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ pointConeDegeneracy =
      (joinStdSimplexIso 0 0).inv := by
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).1
  simp only [pointConeDegeneracy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.F2
