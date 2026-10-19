module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTransport
public import SerrePositivity.InfinityCategories.F1B.KanCosliceOpposite

/-! # 点と点の join の反転と実辺の正規化

概要：両端の点を標準表示で戻すと、join の逆反転は標準辺の逆反転になる。
方針：標準辺の二頂点の値を照合する。
規約：始域・終域を元の標準辺とその反転に固定する。使われ方：通常の屋根頂点の辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 二点の join の順反転は標準辺の反転と一致。 -/
lemma roofJoinReverseEdge_hom :
    SSet.opFunctor.map (joinStdSimplexIso.{u} 0 0).inv ≫
      (stableJoinReverseIso Δ[0] Δ[0]).hom ≫
      joinMap (stdSimplex.opIso ⦋0⦌).hom (stdSimplex.opIso ⦋0⦌).hom ≫
      (joinStdSimplexIso 0 0).hom = (stdSimplex.opIso ⦋1⦌).hom := by
  apply (cancel_epi (stdSimplex.opIso ⦋1⦌).inv).mp
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 二点の join の逆反転を標準辺で評価する。 -/
lemma roofJoinReverseEdge :
    (joinStdSimplexIso.{u} 0 0).inv ≫
      joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      (stableJoinReverseIso Δ[0] Δ[0]).inv ≫
      SSet.opFunctor.map (joinStdSimplexIso 0 0).hom = (stdSimplex.opIso ⦋1⦌).inv := by
  let e := SSet.opFunctor.mapIso (joinStdSimplexIso.{u} 0 0).symm ≪≫
    stableJoinReverseIso Δ[0] Δ[0] ≪≫
    joinIso (stdSimplex.opIso ⦋0⦌) (stdSimplex.opIso ⦋0⦌) ≪≫ joinStdSimplexIso 0 0
  have he : e = stdSimplex.opIso ⦋1⦌ := Iso.ext roofJoinReverseEdge_hom
  have h := congrArg Iso.inv he
  simpa only [e, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, joinIso, Category.assoc] using h

end SerrePositivity.InfinityCategories
