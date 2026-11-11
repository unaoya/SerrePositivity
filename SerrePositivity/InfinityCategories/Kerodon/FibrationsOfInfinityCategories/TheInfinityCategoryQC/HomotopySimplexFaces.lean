module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-!
概要：円柱の面と頂点の垂直辺の一次単体の表示。
方針：空間と時刻の座標の面を別々に計算する。
規約：新しい辺や三角形を選択しない。
使われ方：指定された比較円柱の二次の可換性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：円柱上の射の像の面は二成分の面の像。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopySimplex_face {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) {n : ℕ}
    (x : X _⦋n + 1⦌) (t : (Δ[1] : SSet.{u}) _⦋n + 1⦌) (j : Fin (n + 2)) :
    Y.δ j (H.app (Opposite.op ⦋n + 1⦌) (x, t)) =
      H.app (Opposite.op ⦋n⦌) (X.δ j x, (Δ[1] : SSet.{u}).δ j t) := by
  exact (ConcreteCategory.congr_hom (H.naturality (SimplexCategory.δ j).op)
    (show (X ⊗ Δ[1]) _⦋n + 1⦌ from (x, t))).symm
/-- 概要：標準区間の辺は恒等射の Yoneda 表示。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopyIntervalEdge_simplex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
  apply stdSimplex.ext
  intro j
  fin_cases j <;> rfl
/-- 概要：ホモトピーの垂直辺は定値な空間座標と区間の辺の像。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopyVertexEdge_simplex {X Y : SSet.{u}} {f g : X ⟶ Y}
    (G : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G x).edge =
      G.h.app (Opposite.op ⦋1⦌) (X.σ 0 x, SSet.yonedaEquiv (𝟙 Δ[1])) := by
  change G.h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [homotopyIntervalEdge_simplex]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
