module
public import SerrePositivity.InfinityCategories.Stable.SquareDiagonal
public import SerrePositivity.InfinityCategories.Core.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.Core.HomotopyInvertibility

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma exists_squareDiagonalArrow_equivalence {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (h : IsInvertibleEdge (squareLeftArrow F)) :
    ∃ e : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (functorVertex (SSet.yonedaEquiv.symm (squareDiagonalArrow F).edge))
      (functorVertex (SSet.yonedaEquiv.symm (squareTopArrow F).edge)),
      IsInvertibleEdge e := by
  let b := Truncated.Edge.id (X := (truncation 2).obj X) (squareVertex F 1 1)
  have hb : IsInvertibleEdge b := by
    change IsIso (Truncated.HomotopyCategory.homMk b)
    dsimp only [b]
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hc : Truncated.HomotopyCategory.homMk (squareDiagonalArrow F) ≫
      Truncated.HomotopyCategory.homMk b =
        Truncated.HomotopyCategory.homMk (squareLeftArrow F) ≫
          Truncated.HomotopyCategory.homMk (squareTopArrow F) := by
    simpa only [b, Truncated.HomotopyCategory.homMk_id, Category.comp_id] using
      (squareLeftTop_homMk_diagonal F).symm
  obtain ⟨H, h₀, h₁⟩ := exists_arrowHomotopy_of_homMk_comm
    (squareDiagonalArrow F) (squareTopArrow F) (squareLeftArrow F) b hc
  exact ⟨functorEdgeOfSimplicialHomotopy H,
    arrowHomotopy_isInvertible_of_endpointPaths H (squareLeftArrow F) b h hb h₀ h₁⟩

end SerrePositivity.InfinityCategories
