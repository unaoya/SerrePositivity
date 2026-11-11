module

public import SerrePositivity.KST.LocalizingInvariants.FractionTriangleEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalArrowComparison

/-!
概要：元の分数評価三角形を、分子から評価辺への指定比較四角形へ移す。
方針：右辺を潰す固定形状で同じ三角形を引き戻す。
規約：左辺は元の分母、右辺は元の終点で定値。全パラメータの射を保持する。
使われ方：共有する前段分母経路を次辺の比較へそのまま渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 右辺を頂点二へ潰し、左辺を元の分母にする比較形状。 -/
def fractionEvaluationSquareShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap {
    toFun p := if p.1 = 1 then 2 else p.2.castSucc
    monotone' := by decide }

lemma fractionEvaluationSquareShape_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ fractionEvaluationSquareShape.{u} = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma fractionEvaluationSquareShape_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ fractionEvaluationSquareShape.{u} = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma fractionEvaluationSquareShape_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ fractionEvaluationSquareShape.{u} = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma fractionEvaluationSquareShape_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ fractionEvaluationSquareShape.{u} =
      SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W)

/-- 同じ元の評価三角形による、分子から分数評価への全比較四角形族。 -/
def fractionEvaluationSquare : markedSpans X W ⟶
    (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Q :=
  fractionEvaluationTriangle F W hF ≫ (pre fractionEvaluationSquareShape).app Q

lemma fractionEvaluationSquare_bottom : fractionEvaluationSquare F W hF ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app Q =
      markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F ≫
        (pre horn₂₀.ι₀₂).app Q := by
  rw [fractionEvaluationSquare, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    fractionEvaluationSquareShape_bottom]
  have he : horn₂₀.ι₀₂ ≫ (horn 2 0).ι = stdSimplex.δ (1 : Fin 3) := rfl
  rw [← Category.assoc (markedSpanInclusion X W), ← fractionEvaluationTriangle_span F W hF,
    Category.assoc,
    ← NatTrans.comp_app, ← pre_map, he]

lemma fractionEvaluationSquare_top : fractionEvaluationSquare F W hF ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app Q = fractionSpanEvaluation F W hF := by
  rw [fractionEvaluationSquare, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    fractionEvaluationSquareShape_top]
  rfl

lemma fractionEvaluationSquare_left : fractionEvaluationSquare F W hF ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app Q =
      markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F ≫
        (pre horn₂₀.ι₀₁).app Q := by
  rw [fractionEvaluationSquare, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    fractionEvaluationSquareShape_left]
  have he : horn₂₀.ι₀₁ ≫ (horn 2 0).ι = stdSimplex.δ (2 : Fin 3) := rfl
  rw [← Category.assoc (markedSpanInclusion X W), ← fractionEvaluationTriangle_span F W hF,
    Category.assoc,
    ← NatTrans.comp_app, ← pre_map, he]

lemma fractionEvaluationSquare_right : fractionEvaluationSquare F W hF ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app Q =
      fractionEvaluationTriangle F W hF ≫
        (pre (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) :
          (Δ[1] : SSet.{u}) ⟶ Δ[2])).app Q := by
  rw [fractionEvaluationSquare, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    fractionEvaluationSquareShape_right]

end SerrePositivity.KST.LocalizingInvariants
