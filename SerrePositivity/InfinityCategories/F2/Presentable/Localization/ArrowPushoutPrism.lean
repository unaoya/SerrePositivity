module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.Pullback

/-!
概要：pushout 四角形を、恒等射・下辺・上辺を持つ射圏内の四角形へ展開する prism。
方針：時刻と第一座標の最小値を取り、第二座標をそのまま保持する。
規約：二つの評価と四つの頂点で元の形状の厳密な等号を示す。
使われ方：実 Ind 像の span 余極限閉性を、元の辺クラスの pushout 保存へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- (t,(a,b)) を (min(t,a),b) へ写す元の全 prism。 -/
def arrowPushoutPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ intervalMinimum) (snd _ _ ≫ snd _ _)

/-- 零時刻は四角形の左辺へ第二座標で射影する。 -/
lemma arrowPushoutPrism_zero : prismEndpoint 0 (Δ[1] ⊗ Δ[1]) ≫ arrowPushoutPrism.{u} =
    snd _ _ ≫ squareLeftEdge := by
  have hm : prismEndpoint 0 (Δ[1] ⊗ Δ[1]) ≫
      lift (fst _ _) (snd _ _ ≫ fst _ _) = fst _ _ ≫ prismEndpoint 0 Δ[1] := rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, arrowPushoutPrism, lift_fst, squareLeftEdge, SSet.comp_const]
    rw [← Category.assoc, hm, Category.assoc, intervalMinimum_first_zero, SSet.comp_const]
  · rfl

/-- 一時刻は元の四角形を回収する。 -/
lemma arrowPushoutPrism_one : prismEndpoint 1 (Δ[1] ⊗ Δ[1]) ≫ arrowPushoutPrism.{u} =
    𝟙 (Δ[1] ⊗ Δ[1]) := by
  have hm : prismEndpoint 1 (Δ[1] ⊗ Δ[1]) ≫
      lift (fst _ _) (snd _ _ ≫ fst _ _) = fst _ _ ≫ prismEndpoint 1 Δ[1] := rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, arrowPushoutPrism, lift_fst, Category.id_comp]
    rw [← Category.assoc, hm, Category.assoc, intervalMinimum_first_one, Category.comp_id]
  · rfl

/-- 左下の係数頂点では、その頂点の恒等射となる。 -/
lemma arrowPushoutPrism_vertex_zero : prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) =
      SSet.const (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 右下の係数頂点では、元の下辺となる。 -/
lemma arrowPushoutPrism_vertex_bottom : prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) = squareBottomEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 左上の係数頂点では、その頂点の恒等射となる。 -/
lemma arrowPushoutPrism_vertex_left : prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) =
      SSet.const (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 右上の係数頂点では、元の上辺となる。 -/
lemma arrowPushoutPrism_vertex_top : prismVertexEvaluation arrowPushoutPrism.{u}
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = squareTopEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
