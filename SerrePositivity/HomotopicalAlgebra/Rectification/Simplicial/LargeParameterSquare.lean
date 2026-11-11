module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterMapping
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SelectedTriangle

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceEdges

/-!
# 中断した任意モデル源への一般化：LargeParameterSquare

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Fill a square retaining four selected global homotopies。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0445][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0445
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Fill a square retaining four selected global homotopies

Two triangles use one common diagonal. All four original homotopies are
retained as entire maps over the parameter K, with no large model.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LargeParameterSquare

variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P) {K : SSet.{max w v}}
  {e₀ e₁ e₂ e₃ : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P}
  (H₀₁ : SSet.Homotopy e₀ e₁) (H₁₃ : SSet.Homotopy e₁ e₃)
  (H₀₂ : SSet.Homotopy e₀ e₂) (H₂₃ : SSet.Homotopy e₂ e₃)

abbrev diagonal := LargeParameterHomotopy.homotopy hp e₀ e₃

def leftBoundary : SelectedTriangle.Boundary ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) where
  vertex0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₀
  vertex1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₁
  vertex2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₃
  edge01 := curry H₀₁.h
  edge12 := curry H₁₃.h
  edge02 := curry (diagonal hp).h
  edge01_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero H₀₁
  edge01_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one H₀₁
  edge12_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero H₁₃
  edge12_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one H₁₃
  edge02_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero (diagonal hp)
  edge02_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one (diagonal hp)

def rightBoundary : SelectedTriangle.Boundary ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) where
  vertex0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₀
  vertex1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₂
  vertex2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point e₃
  edge01 := curry H₀₂.h
  edge12 := curry H₂₃.h
  edge02 := curry (diagonal hp).h
  edge01_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero H₀₂
  edge01_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one H₀₂
  edge12_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero H₂₃
  edge12_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one H₂₃
  edge02_zero := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero (diagonal hp)
  edge02_one := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one (diagonal hp)

abbrev boundaryData (left : Bool) := if left then leftBoundary hp H₀₁ H₁₃
  else rightBoundary hp H₀₂ H₂₃

def triangle (left : Bool) : K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 2) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P :=
  uncurry (LargeParameterMapping.fillFaces hp K (boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).faces
    (boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).compatible)

lemma triangle_face (left : Bool) (k : Fin 3) :
    K ◁ SSet.stdSimplex.δ k ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ left =
      uncurry ((boundaryData hp H₀₁ H₁₃ H₀₂ H₂₃ left).faces k) :=
  LargeParameterMapping.fillFaces_uncurry_face hp K _ _ k

lemma left_first : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true = H₀₁.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma left_second : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true = H₁₃.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma right_first : K ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false = H₀₂.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma right_second : K ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false = H₂₃.h := by
  rw [triangle_face]
  exact uncurry_curry _

lemma common_diagonal :
    K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ true =
      K ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hp H₀₁ H₁₃ H₀₂ H₂₃ false := by
  rw [triangle_face, triangle_face]
  rfl

end SerrePositivity.SimplicialModel.LargeParameterSquare
