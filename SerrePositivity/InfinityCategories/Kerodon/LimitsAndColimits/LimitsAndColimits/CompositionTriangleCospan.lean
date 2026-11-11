module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleEndpoints

/-!
概要：元の普遍合成三角形の対角と、同じ終点を持つ指定辺を外ホーンへ貼る。
方針：終点の厳密な一致と外ホーンの二辺の pushout を使う。
規約：対角と指定辺の全高次パラメーターを保持する。
使われ方：分類先の残る第二三角形の外ホーン制限を構成する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {X : SSet.{u}} {x y z w : X _⦋0⦌}
  (e : X.Edge x y) (f : X.Edge y z) (g : X.Edge w z)

/-- 元の普遍合成三角形の対角と指定辺を、同じ終点に沿って外ホーンに貼る。 -/
def compositionTriangleCospanDiagram : (horn 2 2 : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f ⟶ X :=
  (horn₂₂.isPushout.map (tensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f))).desc
    ((stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleEvaluation e f)
    (fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm g.edge)
    (by
      change (stdSimplex.δ (0 : Fin 2) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫
          (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleEvaluation e f =
        (stdSimplex.δ (0 : Fin 2) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫
          fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm g.edge
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_diagonal_target, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeFamily_target])

/-- 同じ外ホーンの対角の側は、元の普遍合成三角形の対角。 -/
lemma compositionTriangleCospanDiagram_diagonal :
    (horn₂₂.ι₀₂ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫ compositionTriangleCospanDiagram e f g =
      (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleEvaluation e f :=
  (horn₂₂.isPushout.map (tensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f))).inl_desc _ _ _

/-- 同じ外ホーンの標的の側は、元の指定辺に全パラメーターで定値。 -/
lemma compositionTriangleCospanDiagram_target :
    (horn₂₂.ι₁₂ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫ compositionTriangleCospanDiagram e f g =
      fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) ≫ SSet.yonedaEquiv.symm g.edge :=
  (horn₂₂.isPushout.map (tensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f))).inr_desc _ _ _

/-- 元の合成三角形の全空間を、第二三角形の同じ外ホーンの関手空間へ写す。 -/
def compositionTriangleCospanMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  curry (compositionTriangleCospanDiagram e f g)

/-- 任意のパラメーターの族でも、同じ外ホーンの対角側は元の三角形の対角。 -/
lemma compositionTriangleCospanMap_diagonal {T : SSet.{u}} (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) :
    (horn₂₂.ι₀₂ ▷ T) ≫ uncurry (a ≫ compositionTriangleCospanMap e f g) =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry a := by
  unfold compositionTriangleCospanMap
  rw [uncurry_natural_left, uncurry_curry, ← Category.assoc, ← whisker_exchange,
    Category.assoc, compositionTriangleCospanDiagram_diagonal, ← Category.assoc,
    whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_precomp]

/-- 任意のパラメーターの族でも、同じ外ホーンの標的側は元の指定辺に定値。 -/
lemma compositionTriangleCospanMap_target {T : SSet.{u}} (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) :
    (horn₂₂.ι₁₂ ▷ T) ≫ uncurry (a ≫ compositionTriangleCospanMap e f g) =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  unfold compositionTriangleCospanMap
  rw [uncurry_natural_left, uncurry_curry, ← Category.assoc, ← whisker_exchange,
    Category.assoc, compositionTriangleCospanDiagram_target, ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
