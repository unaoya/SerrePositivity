module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleEndpoints

/-!
概要：同じ合成三角形空間の任意の族も、元の二辺を全パラメーターで保持する。
方針：普遍評価のパラメーター自然性と二面の計算を合成する。
規約：第一三角形の対角を別のものへ選び直さない。
使われ方：外ホーン延長の二三角形を、元の固定成分の正方形へ貼り合わせる。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ全合成三角形の任意の族の最初の面は、元の第一辺に定値。 -/
lemma compositionTriangleFamily_first {T X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) :
    (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry a =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_precomp e f a, ← Category.assoc, ← whisker_exchange,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_first, ← Category.assoc, whiskerLeft_fst]

/-- 同じ全合成三角形の任意の族の最後の面は、元の第二辺に定値。 -/
lemma compositionTriangleFamily_last {T X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry a =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_precomp e f a, ← Category.assoc, ← whisker_exchange,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleEvaluation_last, ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
