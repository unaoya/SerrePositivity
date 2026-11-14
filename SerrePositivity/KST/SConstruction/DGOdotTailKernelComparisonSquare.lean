module
public import SerrePositivity.KST.SConstruction.DGOdotTailKernelLiftTriangle

/-!
概要：採用された厳密合成の下二単体と、同じ対角を持つ指定上二単体を固定 S で貼る。
方針：正方形の二三角形表示の pushout を使用し、両全二単体を厳密に回収する。
規約：上二単体の存在や共通 LT 長方形の三認証は主張しない。
使われ方：K-S• の上二単体の到着時に下指定二単体と干渉せず実比較面を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  (upper : (Δ[2] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R)
  (diagonal : stdSimplex.δ (1 : Fin 3) ≫ upper =
    stdSimplex.δ (1 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d)

/-- 概要：元厳密合成の下二単体と、同じ共有対角を持つ上二単体の実 S 比較面。
方針：指定二単体を正方形の pushout に貼る。
規約：下二単体を対角移送で選び直さない。使われ方：③ の実比較面の組立て。 -/
def dgOdotTailKernelComparisonSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc upper (dgOdotTailKernelLiftTriangle R d) diagonal

/-- 概要：実比較面の上全二単体は入力された指定上二単体そのもの。
方針：pushout の第一制限を回収。規約：全単体の等号。使われ方：K-S• 上比較の保持。 -/
lemma dgOdotTailKernelComparisonSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgOdotTailKernelComparisonSquare R d upper diagonal = upper :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 概要：実比較面の下全二単体は保存済みの厳密合成二単体そのもの。
方針：pushout の第二制限を回収。規約：二辺だけで代用しない。
使われ方：厚核側下指定二単体の厳密保持。 -/
lemma dgOdotTailKernelComparisonSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotTailKernelComparisonSquare R d upper diagonal =
      dgOdotTailKernelLiftTriangle R d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 概要：元実比較面の二下短辺は厚核包含と保存済み実中央辺。
方針：元下二単体の三面回収を使う。規約：全一単体の等号。
使われ方：同じ cell 入力と右面への共有境界。 -/
lemma dgOdotTailKernelComparisonSquare_lower_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotTailKernelComparisonSquare R d upper diagonal =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotTailKernelComparisonSquare R d upper diagonal =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d)).edge := by
  constructor
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge, Category.assoc,
      dgOdotTailKernelComparisonSquare_lower]
    exact (dgOdotTailKernelLiftTriangle_edges R d).1
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, dgOdotTailKernelComparisonSquare_lower]
    exact (dgOdotTailKernelLiftTriangle_edges R d).2.1

/-- 概要：実比較面の左上二短辺も指定上二単体から厳密に回収する。
方針：元上二単体の二面へ制限。規約：上辺を別に選択しない。
使われ方：K-S• の上境界と固定 S の実四辺の同時保持。 -/
lemma dgOdotTailKernelComparisonSquare_upper_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotTailKernelComparisonSquare R d upper diagonal =
        stdSimplex.δ (2 : Fin 3) ≫ upper ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotTailKernelComparisonSquare R d upper diagonal =
        stdSimplex.δ (0 : Fin 3) ≫ upper := by
  constructor
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge, Category.assoc, dgOdotTailKernelComparisonSquare_upper]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, dgOdotTailKernelComparisonSquare_upper]

/-- 概要：同じ実比較面の始点は元厚核入力そのもの。
方針：元下辺の始点回収を使う。規約：同値な別頂点への置換はしない。
使われ方：ActualRectangleInput の kernel_vertex への接続。 -/
lemma dgOdotTailKernelComparisonSquare_kernel_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotTailKernelComparisonSquare R d upper diagonal) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d) := by
  have hv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (dgOdotTailKernelComparisonSquare R d upper diagonal)
  rw [(dgOdotTailKernelComparisonSquare_lower_edges R d upper diagonal).1] at hv
  exact hv.symm.trans ((congrArg ((dgKInputInfinity.{u, u + 1} R).δ 1)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).src_eq)

/-- 概要：同じ実比較面の Cat^perf 像も元下二単体の全 ν 像を厳密に保つ。
方針：固定 ν で後合成するだけ。規約：別の下比較二単体を選択しない。
使われ方：LT の全長方形比較の下二単体の実側。 -/
lemma dgOdotTailKernelComparisonSquare_perfect_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotTailKernelComparisonSquare R d upper diagonal ≫
        dgKInputPerfectNu R = dgOdotTailKernelLiftPerfectTriangle R d := by
  rw [← Category.assoc, dgOdotTailKernelComparisonSquare_lower]
  rfl
end SerrePositivity.KST.SConstruction
