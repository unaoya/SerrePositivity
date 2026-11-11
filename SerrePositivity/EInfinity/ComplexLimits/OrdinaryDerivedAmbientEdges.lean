module

public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedAmbientVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
# 元の通常複体射と同じ閉 dg 辺の導来像

概要：元の複体射の通常導来源による像は、同じ閉辺の分解関手による像に一致する。
方針：元の一次単体の一致と端点等式の明示的輸送を使う。
規約：元の射と同じ分解関手を保つ。
使われ方：元の自由単位の全族公式に現れる辺を既存の単位成分に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexOrdinaryAmbient_edge {X Y : Complex A} (f : X ⟶ Y) :
    ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).edge =
      (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f)).edge := by
  change (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ f) = _
  simp only [complexOrdinaryDerivedSource, NatTrans.comp_app_apply, nerveMap_app_mk₁,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion_mk₁]

lemma complexOrdinaryAmbient_hom {X Y : Complex A} (f : X ⟶ Y) :
    (complexOrdinaryAmbientVertexIso A X).inv ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).toTruncated ≫
      (complexOrdinaryAmbientVertexIso A Y).hom =
    (hoFunctor.map (complexSemifreeResolutionInfinity A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f))) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (complexOrdinaryAmbient_vertex A X)
    (complexOrdinaryAmbient_vertex A Y)
    ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).toTruncated
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f)).map
      ((truncation 2).map (complexSemifreeResolutionInfinity A)))
    (complexOrdinaryAmbient_edge A f)

end SerrePositivity.EInfinity.ComplexLimits
