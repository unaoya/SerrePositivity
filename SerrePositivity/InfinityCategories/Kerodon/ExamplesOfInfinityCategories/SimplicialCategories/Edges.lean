module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常の射と合成を coherent nerve の辺と三角形として表す。
方針：通常の nerve からの標準射で辺と二単体を写す。
規約：単体的圏の局所 Kan 性は仮定しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、𝒮 の辺と pointed space の構成。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：通常の射が定める coherent nerve の辺。
方針：通常の nerve の辺を写し、頂点の計算で端点を合わせる。
規約：端点は coherentNerveVertex で指定する。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、空間の間の写像の coherent な表示。 -/
noncomputable def coherentNerveEdge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) :=
  ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C)).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_vertex Y)

/-- 概要：通常の射から作った辺の一単体を計算する。
方針：辺の写像と端点の変更の定義を展開する。
規約：通常の射は ComposableArrows.mk₁ で表示する。
使われ方：Kerodon §2.4.3（Tag 00KM）、合成三角形の面の計算。 -/
lemma coherentNerveEdge_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) := rfl

/-- 概要：恒等射は coherent nerve の恒等辺を与える。
方針：通常の nerve の退化と標準射の自然性を使う。
規約：辺の等号は一単体の等号で証明する。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、pointed space の恒等写像。 -/
lemma coherentNerveEdge_id {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    coherentNerveEdge (𝟙 X) = SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := by
  apply SSet.Edge.ext
  rw [coherentNerveEdge_edge, SSet.Edge.id_edge,
    ← nerve.σ₀_mk₀_eq, σ_naturality_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_vertex]

/-- 概要：通常の合成は coherent nerve 内の合成三角形を与える。
方針：ComposableArrows.mk₂ を標準射で写し、三面を自然性で計算する。
規約：選んだ三角形を返し、合成辺の一意性は主張しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、strict な合成の coherent な証人。 -/
noncomputable def coherentNerveCompStruct {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.Edge.CompStruct (coherentNerveEdge f) (coherentNerveEdge g)
      (coherentNerveEdge (f ≫ g)) :=
  SSet.Edge.CompStruct.mk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ f g))
    (by rw [← δ_naturality_apply, nerve.δ₂_mk₂_eq, coherentNerveEdge_edge])
    (by rw [← δ_naturality_apply, nerve.δ₀_mk₂_eq, coherentNerveEdge_edge])
    (by rw [← δ_naturality_apply, nerve.δ₁_mk₂_eq, coherentNerveEdge_edge])

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
