module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.OrdinalSimplexEdges

/-!
概要：後ろ三頂点を同じ点に固定した元の三単体で、内辺が定値なら左辺と右辺の合成は外辺。
方針：元の二つの三角形の合成構造を、指定した頂点へ移送してホモトピー圏で比較する。
規約：元の辺の一単体を保持。使われ方：edgewise 解像で二つの零ホモトピーの差を計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FramedTetrahedron
end SerrePositivity.KST.Spectra.FramedTetrahedron
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.FramedTetrahedron

/-- 初点と、後ろ三頂点の共通点からなる元の頂点表示。 -/
abbrev vertex {X : SSet.{u}} (p x : X _⦋0⦌) (i : Fin 4) : X _⦋0⦌ := if i = 0 then p else x

/-- 元の三単体の同じ辺を、指定した二点の表示へ移送したもの。 -/
def edge {X : SSet.{u}} (f : (Δ[3] : SSet.{u}) ⟶ X) (p x : X _⦋0⦌)
    (hv : ∀ i : Fin 4, f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x i)
    (i j : Fin 4) (hij : i ≤ j) : X.Edge (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x i) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x j) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge i j hij).map f).ofEq (hv i) (hv j)

/-- 元の内辺が定値なら、元の左辺と右辺の合成は元の外辺に等しい。 -/
lemma left_comp_right {X : SSet.{u}} (f : (Δ[3] : SSet.{u}) ⟶ X) (p x : X _⦋0⦌)
    (hv : ∀ i : Fin 4, f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.vertex p x i)
    (hi : f.app (Opposite.op ⦋1⦌) (stdSimplex.edge 3 1 2 (by decide)) = (X.σ 0) x) :
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 1 (by decide)) ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 2 3 (by decide)) =
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 3 (by decide)) := by
  have h₀₁₂ : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 1 (by decide))
      (SSet.Edge.id x) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 2 (by decide)) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 4) 1 2 (by decide) (by decide)).map f).ofEq
      rfl hi rfl
  have h₀₂₃ : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 2 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 2 3 (by decide)) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.edge f p x hv 0 3 (by decide)) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 4) 2 3 (by decide) (by decide)).map f).ofEq
      rfl rfl rfl
  have hl := SSet.HomotopyCategory.homMk_comp_homMk h₀₁₂
  erw [SSet.HomotopyCategory.homMk_id, Category.comp_id] at hl
  rw [hl]
  exact SSet.HomotopyCategory.homMk_comp_homMk h₀₂₃

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
