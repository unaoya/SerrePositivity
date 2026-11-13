module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.OrdinalSimplexEdges
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangleOuterFaces

/-!
概要：単体的正方形の外周の二つの合成は、同じ対角辺の類に等しい。
方針：上側と下側の実際の二単体の合成構造を使う。
規約：Kan 条件不要。使われ方：比較 Hom 正方形から共通の中央経路を消去する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.SquareBoundary
end SerrePositivity.KST.Spectra.SquareBoundary
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.SquareBoundary

/-- 正方形の指定した隅。 -/
abbrev corner (i j : Fin 2) : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

/-- 上側の三角形の元の左辺。 -/
def left : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 1) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 1 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq rfl rfl

/-- 上側の三角形の元の上辺。 -/
def top : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 1) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (1 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq rfl rfl

/-- 下側の三角形の元の下辺。 -/
def bottom : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 1 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower).ofEq rfl rfl

/-- 下側の三角形の元の右辺。 -/
def right : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (1 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower).ofEq rfl rfl

/-- 元の left 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma left_yoneda : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left.edge =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の right 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma right_yoneda : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right.edge =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の bottom 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma bottom_yoneda : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom.edge =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の top 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma top_yoneda : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top.edge =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 二つの三角形の対角辺は、同じ元の一単体。 -/
lemma diagonal_edge :
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq
      (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0 from rfl) (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1 from rfl)) =
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower).ofEq
      (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0 from rfl) (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1 from rfl)) := by
  apply SSet.Edge.ext
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の二つの三角形により、下辺・右辺の合成は左辺・上辺の合成に等しい。 -/
lemma composition {X : SSet.{u}} (q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom.map q) ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right.map q) =
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left.map q) ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top.map q) := by
  have hu : SSet.Edge.CompStruct _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top
      (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq
        (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0 from rfl) (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1 from rfl)) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq rfl rfl rfl
  have hl : SSet.Edge.CompStruct _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right
      (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).ofEq
        (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0 from rfl) (show _ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1 from rfl)) :=
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower).ofEq rfl rfl (congrArg SSet.Edge.edge _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.diagonal_edge.symm)
  rw [SSet.HomotopyCategory.homMk_comp_homMk (hl.map q),
    SSet.HomotopyCategory.homMk_comp_homMk (hu.map q)]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom_yoneda := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom_yoneda

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.composition := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.composition

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.corner := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.diagonal_edge := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.diagonal_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left_yoneda := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left_yoneda

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right_yoneda := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right_yoneda

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top_yoneda := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top_yoneda

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.diagonal_edge._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.diagonal_edge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top._proof_3
