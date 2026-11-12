module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-!
概要：pushout 四角形を、恒等射・下辺・上辺を持つ射圏内の四角形へ展開する prism。
方針：時刻と第一座標の最小値を取り、第二座標をそのまま保持する。
規約：二つの評価と四つの頂点で元の形状の厳密な等号を示す。
使われ方：実 Ind 像の span 余極限閉性を、元の辺クラスの pushout 保存へ移す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- (t,(a,b)) を (min(t,a),b) へ写す元の全 prism。 -/
def arrowPushoutPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum) (snd _ _ ≫ snd _ _)

/-- 零時刻は四角形の左辺へ第二座標で射影する。 -/
lemma arrowPushoutPrism_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1]) ≫ arrowPushoutPrism.{u} =
    snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1]) ≫
      lift (fst _ _) (snd _ _ ≫ fst _ _) = fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, arrowPushoutPrism, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, SSet.comp_const]
    rw [← Category.assoc, hm, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_zero, SSet.comp_const]
  · rfl

/-- 一時刻は元の四角形を回収する。 -/
lemma arrowPushoutPrism_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1]) ≫ arrowPushoutPrism.{u} =
    𝟙 (Δ[1] ⊗ Δ[1]) := by
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1]) ≫
      lift (fst _ _) (snd _ _ ≫ fst _ _) = fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, arrowPushoutPrism, lift_fst, Category.id_comp]
    rw [← Category.assoc, hm, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_one, Category.comp_id]
  · rfl

/-- 左下の係数頂点では、その頂点の恒等射となる。 -/
lemma arrowPushoutPrism_vertex_zero : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
      SSet.const (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 右下の係数頂点では、元の下辺となる。 -/
lemma arrowPushoutPrism_vertex_bottom : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 左上の係数頂点では、その頂点の恒等射となる。 -/
lemma arrowPushoutPrism_vertex_left : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
      SSet.const (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 右上の係数頂点では、元の上辺となる。 -/
lemma arrowPushoutPrism_vertex_top : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
