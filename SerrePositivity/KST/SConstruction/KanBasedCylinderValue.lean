module
public import SerrePositivity.KST.SConstruction.KanBasedEdgeValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangleOuterFaces

/-! # 全端点固定円柱による基点表示の不変性
概要：元の円柱の全境界固定式から、入口と出口の辺の同じ群値を回収する。
方針：円柱の二つの全三角形の合成式を、定数の両縦辺を使って比較する。
規約：円柱全体と境界固定式を入力に使い、二辺の類の一致を別仮定に置かない。
使われ方：十二面複体の正規化円柱と共有直接比較円柱による辺路の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped _root_.Simplicial
variable {E : SSet.{u}} [KanComplex E]
local instance kanBasedCylinderValueGroupoid : Groupoid (hoFunctor.obj E) :=
  Groupoid.ofIsGroupoid
variable (c : hoFunctor.obj E)

/-- 定数辺の値は元の同じ頂点での恒等元。 -/
lemma kanBasedEdgeValue_const (x : E _⦋0⦌) :
    kanBasedEdgeValue c (SSet.const x) = 1 := by
  rw [← mappingIdentityEdge_map x, kanBasedEdgeValue_edge,
    SSet.HomotopyCategory.homMk_id, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.groupoidBasedArrow_id]

/-- 元の全正方形は、その同じ四辺の二通りの積の等号を与える。 -/
lemma kanBasedEdgeValue_square (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) :
    kanBasedEdgeValue c (pastingSquareVertical 1 ≫ Q) *
        kanBasedEdgeValue c (SSet.ι₀ ≫ Q) =
      kanBasedEdgeValue c (SSet.ι₁ ≫ Q) *
        kanBasedEdgeValue c (pastingSquareVertical 0 ≫ Q) := by
  have hl := kanBasedEdgeValue_triangle c (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ Q)
  have hu := kanBasedEdgeValue_triangle c (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ Q)
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_diagonal,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_face_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_face_last] at hl
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_diagonal,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_last] at hu
  exact hl.symm.trans hu

/-- 両縦辺が元の同じ定数辺なら、正方形の全横辺の値は等しい。 -/
lemma kanBasedEdgeValue_fixedSquare (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
    (x y : E _⦋0⦌)
    (hx : pastingSquareVertical 0 ≫ Q = SSet.const x)
    (hy : pastingSquareVertical 1 ≫ Q = SSet.const y) :
    kanBasedEdgeValue c (SSet.ι₀ ≫ Q) = kanBasedEdgeValue c (SSet.ι₁ ≫ Q) := by
  have h := kanBasedEdgeValue_square c Q
  rw [hx, hy, kanBasedEdgeValue_const, kanBasedEdgeValue_const, one_mul, mul_one] at h
  exact h

/-- 元の端点固定全円柱の入口・出口は同じ基点表示を持つ。 -/
lemma EndpointFixedEdgeCylinder.basedValue {x y : E _⦋0⦌} {a b : E.Edge x y}
    (H : EndpointFixedEdgeCylinder a b) :
    kanBasedEdgeValue c (SSet.yonedaEquiv.symm a.edge) =
      kanBasedEdgeValue c (SSet.yonedaEquiv.symm b.edge) := by
  have hv (i : Fin 2) :
      pastingSquareVertical i ≫ H.homotopy.h =
        SSet.const (if i = 0 then x else y) := by
    fin_cases i
    · change pastingSquareVertical 0 ≫ H.homotopy.h = SSet.const x
      have hp : pastingSquareVertical.{u} 0 =
          lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
            (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
        rw [stdSimplex.δ_one_eq_const]
        rfl
      rw [hp, Category.assoc, H.vertex 1, SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]
    · change pastingSquareVertical 1 ≫ H.homotopy.h = SSet.const y
      have hp : pastingSquareVertical.{u} 1 =
          lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
            (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
        rw [stdSimplex.δ_zero_eq_const]
        rfl
      rw [hp, Category.assoc, H.vertex 0, SSet.Edge.δ_zero_yonedaEquiv_symm,
        SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]
  have h := kanBasedEdgeValue_fixedSquare c H.homotopy.h x y (hv 0) (hv 1)
  rw [H.homotopy.h₀, H.homotopy.h₁] at h
  exact h

/-- 全入力境界を固定する実正方形は、入口と出口の全辺の値を保つ。 -/
lemma kanBasedEdgeValue_relative (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
    (a : (Δ[1] : SSet.{u}) ⟶ E)
    (hr : ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ Q =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫ a) :
    kanBasedEdgeValue c (SSet.ι₀ ≫ Q) = kanBasedEdgeValue c (SSet.ι₁ ≫ Q) := by
  have hv (i : Fin 2) :
      (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ Q =
        fst (Δ[0] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ a := by
    rw [← SSet.boundary.ι_ι i, comp_whiskerRight, Category.assoc, hr,
      whiskerRight_fst_assoc, Category.assoc, SSet.boundary.ι_ι_assoc]
  have hconst (i : Fin 2) :
      pastingSquareVertical (if i = 1 then 0 else 1) ≫ Q =
        SSet.const (SSet.yonedaEquiv (stdSimplex.δ i ≫ a)) := by
    have he : stdSimplex.δ i ≫ a =
        SSet.const (SSet.yonedaEquiv (stdSimplex.δ i ≫ a)) := by
      rw [← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]
    fin_cases i
    · change pastingSquareVertical 1 ≫ Q = _
      have hp : pastingSquareVertical.{u} 1 =
          lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
            (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
        rw [stdSimplex.δ_zero_eq_const]
        rfl
      change stdSimplex.δ.{u} (0 : Fin 2) ≫ a =
        SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a)) at he
      rw [hp, Category.assoc, hv 0]
      conv_lhs =>
        rw [he]
        simp only [SSet.comp_const]
      rfl
    · change pastingSquareVertical 0 ≫ Q = _
      have hp : pastingSquareVertical.{u} 0 =
          lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
            (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
        rw [stdSimplex.δ_one_eq_const]
        rfl
      change stdSimplex.δ.{u} (1 : Fin 2) ≫ a =
        SSet.const (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) at he
      rw [hp, Category.assoc, hv 1]
      conv_lhs =>
        rw [he]
        simp only [SSet.comp_const]
      rfl
  exact kanBasedEdgeValue_fixedSquare c Q _ _ (hconst 1) (hconst 0)

end SerrePositivity.KST.SConstruction
