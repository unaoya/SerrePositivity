module
public import SerrePositivity.InfinityCategories.Derived.RoofJoinReverseEdge

/-! # 反転した実 coslice 頂点から回収する辺

概要：固定点を戻した反転 slice の辺は、元の coslice の辺の反転そのもの。
方針：点の二つの反転を join の逆反転と合成し、標準辺の反転へ戻す。
規約：標的は任意の単体集合。使われ方：通常の over 比較の指定構造射の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- coslice の反転で得た slice 頂点の辺を標準辺の反転として読む。 -/
lemma roofReverseVertexEdge {X : SSet.{u}} (a : Δ[0] ⟶ X) (s : (sliceUnder a) _⦋0⦌) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((F1B.kanSliceUnderOpMap a).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm s)).val) =
        SSet.opObjEquiv.symm (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s.val)) := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
    (F1B.kanSliceUnderOpObjEquiv a ⦋0⦌ (SSet.opObjEquiv.symm s)).val) = _
  rw [F1B.kanSliceUnderOpObjEquiv_val]
  simp only [Equiv.apply_symm_apply]
  rw [← Category.assoc (joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv)
    (joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (Δ[0] : SSet.{u}).op)) _, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]
  let e := (joinStdSimplexIso 0 0).inv ≫ s.val
  have hs : s.val = (joinStdSimplexIso 0 0).hom ≫ e := by
    dsimp [e]
    rw [Iso.hom_inv_id_assoc]
  have he : (joinStdSimplexIso 0 0).inv ≫
      joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      (stableJoinReverseIso Δ[0] Δ[0]).inv ≫ SSet.opFunctor.map s.val =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map e := by
    rw [hs, SSet.opFunctor.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ SSet.opFunctor.map e) roofJoinReverseEdge
  rw [he, stableReverseSimplex_yoneda]

end SerrePositivity.InfinityCategories
