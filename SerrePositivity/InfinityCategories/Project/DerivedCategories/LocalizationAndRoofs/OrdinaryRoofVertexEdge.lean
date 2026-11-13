module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.OrdinaryRoofVertexData
public import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso

/-! # 通常の over nerve 比較の指定構造射

概要：通常の over 比較の零単体から、元の指定構造射の nerve 辺を回収する。
方針：固定図式の輸送を外し、反対 Under の辺の表示を計算する。
規約：F1B は読み取り専用。使われ方：厳密屋根比較の実分母全部分圏への因子化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {C : Type u} [Category.{u} C]

/-- 反対 Under を経由した生の over 頂点の表示。 -/
lemma ordinaryRoofRawVertex (c : C) (s : Over c) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))).app _
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderSimplex (op c)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((Under.opEquivOpOver c).inverse.obj (op s))))) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))).app _
    ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap (op c))).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverOppositeUnderIso c).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ordinaryRoofOppositeVertex]
  rfl

/-- 生の over 頂点の辺は反対構造射の反転。 -/
lemma ordinaryRoofRawVertexEdge (c : C) (s : Over c) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)).val) = SSet.opObjEquiv.symm
          (ComposableArrows.mk₁ ((Under.opEquivOpOver c).inverse.obj (op s)).hom) := by
  rw [ordinaryRoofRawVertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofReverseVertexEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ordinaryUnderVertexEdge]

/-- 反対構造射を戻すと元の構造射の nerve 辺。 -/
lemma ordinaryRoofUnopEdge (c : C) (s : Over c) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (ComposableArrows.mk₁
        ((Under.opEquivOpOver c).inverse.obj (op s)).hom)) =
      ComposableArrows.mk₁ s.hom := by
  let u := (Under.opEquivOpOver c).inverse.obj (op s)
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplex (ComposableArrows.mk₁ u.hom) =
    ComposableArrows.mk₁ s.hom
  refine ComposableArrows.ext₁
    (F := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplex (ComposableArrows.mk₁ u.hom))
    (G := ComposableArrows.mk₁ s.hom) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 通常の over 比較の指定対象の実辺は、元の構造射の nerve 辺。 -/
lemma ordinaryRoofVertexEdge (c : C) (s : Over c) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)
      ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))).edge =
        ComposableArrows.mk₁ s.hom := by
  let p := SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))
  let q := (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom
  let t := (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverBase_eq c))).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q).app _ t)))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofSliceTransport_edge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverBase_eq c)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofSlicePostRestrict_edge p q (stdSimplex.opIso ⦋0⦌).inv t]
  change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)).val)) = _
  rw [ordinaryRoofRawVertexEdge]
  exact ordinaryRoofUnopEdge c s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
