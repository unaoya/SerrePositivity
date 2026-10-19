module
public import SerrePositivity.InfinityCategories.Derived.OrdinaryRoofVertexData
public import SerrePositivity.InfinityCategories.F1B.KanNerveOverIso

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite SSet
open scoped Simplicial
variable {C : Type u} [Category.{u} C]

/-- 反対 Under を経由した生の over 頂点の表示。 -/
lemma ordinaryRoofRawVertex (c : C) (s : Over c) :
    (F1B.kanNerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex s) =
      (F1B.kanSliceUnderOpMap (nervePoint (op c))).app _
        (SSet.opObjEquiv.symm (F1B.kanNerveUnderSimplex (op c)
          (nerveVertex ((Under.opEquivOpOver c).inverse.obj (op s))))) := by
  change (F1B.kanSliceUnderOpMap (nervePoint (op c))).app _
    ((SSet.opFunctor.map (F1B.kanNerveUnderMap (op c))).app _
      ((F1B.kanNerveOverOppositeUnderIso c).hom.app _ (nerveVertex s))) = _
  rw [ordinaryRoofOppositeVertex]
  rfl

/-- 生の over 頂点の辺は反対構造射の反転。 -/
lemma ordinaryRoofRawVertexEdge (c : C) (s : Over c) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((F1B.kanNerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌)
        (nerveVertex s)).val) = SSet.opObjEquiv.symm
          (ComposableArrows.mk₁ ((Under.opEquivOpOver c).inverse.obj (op s)).hom) := by
  rw [ordinaryRoofRawVertex, roofReverseVertexEdge, ordinaryUnderVertexEdge]

/-- 反対構造射を戻すと元の構造射の nerve 辺。 -/
lemma ordinaryRoofUnopEdge (c : C) (s : Over c) :
    (F1B.kanNerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (ComposableArrows.mk₁
        ((Under.opEquivOpOver c).inverse.obj (op s)).hom)) =
      ComposableArrows.mk₁ s.hom := by
  let u := (Under.opEquivOpOver c).inverse.obj (op s)
  change F1B.kanOppositeNerveSimplex (ComposableArrows.mk₁ u.hom) =
    ComposableArrows.mk₁ s.hom
  refine ComposableArrows.ext₁
    (F := F1B.kanOppositeNerveSimplex (ComposableArrows.mk₁ u.hom))
    (G := ComposableArrows.mk₁ s.hom) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 通常の over 比較の指定対象の実辺は、元の構造射の nerve 辺。 -/
lemma ordinaryRoofVertexEdge (c : C) (s : Over c) :
    (roofPointSliceVertexEdge (nervePoint c)
      ((F1B.kanNerveOverIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex s))).edge =
        ComposableArrows.mk₁ s.hom := by
  let p := SSet.opFunctor.map (nervePoint (op c))
  let q := (F1B.kanNerveUnopIso C).hom
  let t := (F1B.kanNerveOverRawSliceIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex s)
  change (roofPointSliceVertexEdge (nervePoint c)
    ((eqToIso (congrArg sliceOver (F1B.kanNerveOverBase_eq c))).hom.app _
      ((sliceOverRestrict (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv).app _
        ((sliceOverPostcomp p q).app _ t)))).edge = _
  rw [roofSliceTransport_edge (F1B.kanNerveOverBase_eq c)]
  rw [roofSlicePostRestrict_edge p q (stdSimplex.opIso ⦋0⦌).inv t]
  change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
    ((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (stdSimplex.opIso ⦋0⦌).inv ≫
      ((F1B.kanNerveOverRawSliceIso c).hom.app _ (nerveVertex s)).val)) = _
  rw [ordinaryRoofRawVertexEdge]
  exact ordinaryRoofUnopEdge c s

end SerrePositivity.InfinityCategories
