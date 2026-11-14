module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.OrdinaryRoofVertexEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGClosedNerveOverMap

/-! # 閉 over nerve 比較の指定頂点

概要：厳密 over 比較の零単体は、指定閉構造射から直接作った実 slice 頂点に一致する。
方針：固定図式の輸送と後合成を外し、通常の over の構造射の計算へ戻す。
規約：対象と Hom の独立宇宙を保持する。使われ方：実分母全部分圏への因子化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 共通宇宙へ上げた閉構造射の nerve 辺を、元の閉圏へ戻す。 -/
lemma dgCommonClosedNerveDown_edge {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNerveDown A D).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ ((AsSmall.up : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D ⥤
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonClosedCategory A D).map s)) = ComposableArrows.mk₁ s := by
  refine ComposableArrows.ext₁ (F := _ ⋙ AsSmall.down)
    (G := ComposableArrows.mk₁ s) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 厳密閉 over 比較から回収した実辺は元の指定構造射の実辺。 -/
lemma dgClosedNerveOverMap_edge (x : D)
    (s : Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))).edge =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s.hom).edge := by
  let c := (AsSmall.up : ClosedCategory A D ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonClosedCategory A D).obj
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
  let t := (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((Over.post (AsSmall.up : ClosedCategory A D ⥤
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonClosedCategory A D)).obj s))
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNervePoint A D x))).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNerveToDG A D)).app _ t))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofSliceTransport_edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNervePoint A D x),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_postcomp]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNerveToDG A D).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) t).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ordinaryRoofVertexEdge]
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonClosedNerveDown A D).app _ (ComposableArrows.mk₁
      ((AsSmall.up : ClosedCategory A D ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonClosedCategory A D).map s.hom))) = _
  rw [dgCommonClosedNerveDown_edge]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv A D).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_edge]
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    rfl

/-- 比較で得た実 slice 頂点は、元の閉構造射から作った頂点そのもの。 -/
lemma dgClosedNerveOverMap_vertex (x : D)
    (s : Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D s.hom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
  exact (dgClosedNerveOverMap_edge A D x s).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D s.hom).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
