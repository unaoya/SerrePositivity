module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofJoinReverseEdge

/-! # 反転した実 coslice 頂点から回収する辺

概要：固定点を戻した反転 slice の辺は、元の coslice の辺の反転そのもの。
方針：点の二つの反転を join の逆反転と合成し、標準辺の反転へ戻す。
規約：標的は任意の単体集合。使われ方：通常の over 比較の指定構造射の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- coslice の反転で得た slice 頂点の辺を標準辺の反転として読む。 -/
lemma roofReverseVertexEdge {X : SSet.{u}} (a : Δ[0] ⟶ X) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpMap a).app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm s)).val) =
        SSet.opObjEquiv.symm (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ s.val)) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv a ⦋0⦌ (SSet.opObjEquiv.symm s)).val) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv_val]
  simp only [Equiv.apply_symm_apply]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (Δ[0] : SSet.{u}).op)) _, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ s.val
  have hs : s.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ e := by
    dsimp [e]
    rw [Iso.hom_inv_id_assoc]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[0]).inv ≫ SSet.opFunctor.map s.val =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map e := by
    rw [hs, SSet.opFunctor.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ SSet.opFunctor.map e) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofJoinReverseEdge
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
