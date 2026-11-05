module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.OrdinalSimplexEdges
public import SerrePositivity.InfinityCategories.Simplicial.SquareTriangleOuterFaces

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
namespace SerrePositivity.InfinityCategories.Kan.SquareBoundary
open SerrePositivity.KST.Spectra.SquareBoundary

/-- 正方形の指定した隅。 -/
abbrev corner (i j : Fin 2) : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
  (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

/-- 上側の三角形の元の左辺。 -/
def left : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (corner 0 0) (corner 0 1) :=
  ((SimplexEdges.edge (0 : Fin 3) 1 (by decide)).map SquareTriangles.upper).ofEq rfl rfl

/-- 上側の三角形の元の上辺。 -/
def top : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (corner 0 1) (corner 1 1) :=
  ((SimplexEdges.edge (1 : Fin 3) 2 (by decide)).map SquareTriangles.upper).ofEq rfl rfl

/-- 下側の三角形の元の下辺。 -/
def bottom : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (corner 0 0) (corner 1 0) :=
  ((SimplexEdges.edge (0 : Fin 3) 1 (by decide)).map SquareTriangles.lower).ofEq rfl rfl

/-- 下側の三角形の元の右辺。 -/
def right : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Edge (corner 1 0) (corner 1 1) :=
  ((SimplexEdges.edge (1 : Fin 3) 2 (by decide)).map SquareTriangles.lower).ofEq rfl rfl

/-- 元の left 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma left_yoneda : SSet.yonedaEquiv.symm left.edge =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の right 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma right_yoneda : SSet.yonedaEquiv.symm right.edge =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の bottom 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma bottom_yoneda : SSet.yonedaEquiv.symm bottom.edge =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の top 辺の Yoneda 射は、同じ座標辺の包含。 -/
lemma top_yoneda : SSet.yonedaEquiv.symm top.edge =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 二つの三角形の対角辺は、同じ元の一単体。 -/
lemma diagonal_edge :
    (((SimplexEdges.edge (0 : Fin 3) 2 (by decide)).map SquareTriangles.upper).ofEq
      (show _ = corner 0 0 from rfl) (show _ = corner 1 1 from rfl)) =
    (((SimplexEdges.edge (0 : Fin 3) 2 (by decide)).map SquareTriangles.lower).ofEq
      (show _ = corner 0 0 from rfl) (show _ = corner 1 1 from rfl)) := by
  apply SSet.Edge.ext
  apply Prod.ext
  all_goals
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の二つの三角形により、下辺・右辺の合成は左辺・上辺の合成に等しい。 -/
lemma composition {X : SSet.{u}} (q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.HomotopyCategory.homMk (bottom.map q) ≫
      SSet.HomotopyCategory.homMk (right.map q) =
    SSet.HomotopyCategory.homMk (left.map q) ≫
      SSet.HomotopyCategory.homMk (top.map q) := by
  have hu : SSet.Edge.CompStruct left top
      (((SimplexEdges.edge (0 : Fin 3) 2 (by decide)).map SquareTriangles.upper).ofEq
        (show _ = corner 0 0 from rfl) (show _ = corner 1 1 from rfl)) :=
    ((SimplexEdges.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      SquareTriangles.upper).ofEq rfl rfl rfl
  have hl : SSet.Edge.CompStruct bottom right
      (((SimplexEdges.edge (0 : Fin 3) 2 (by decide)).map SquareTriangles.upper).ofEq
        (show _ = corner 0 0 from rfl) (show _ = corner 1 1 from rfl)) :=
    ((SimplexEdges.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      SquareTriangles.lower).ofEq rfl rfl (congrArg SSet.Edge.edge diagonal_edge.symm)
  rw [SSet.HomotopyCategory.homMk_comp_homMk (hl.map q),
    SSet.HomotopyCategory.homMk_comp_homMk (hu.map q)]

end SerrePositivity.InfinityCategories.Kan.SquareBoundary

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom_yoneda := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.bottom_yoneda

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.composition := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.composition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.corner (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.corner := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.corner

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.diagonal_edge := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.diagonal_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left_yoneda := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left_yoneda

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right_yoneda := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.right_yoneda

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top_yoneda := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top_yoneda

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.bottom._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.bottom._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.bottom._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.diagonal_edge._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.diagonal_edge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.left._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.left._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.right._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.right._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.right._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SquareBoundary.top._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.SquareBoundary.top._proof_3
