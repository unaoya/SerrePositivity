module

public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.CatInfinity.HomotopySimplexFaces
public import SerrePositivity.InfinityCategories.Core.CatInfinity.TrianglePrismUpperSides
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：辺の比較正方形の上側の三角形の三辺。
方針：空間と時刻の座標の面を別々に計算する。
規約：新しい辺や三角形を選択しない。
使われ方：指定された比較円柱の二次の可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：上側の三角形の底辺は時刻一の辺の像。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopyEdgeTriangleUpper_zero {X Y : SSet.{u}} {f g : X ⟶ Y}
    (G : SSet.Homotopy f g) (t : X _⦋1⦌) :
    Y.δ 0 (homotopyEdgeTriangleUpper G.h t) = g.app (Opposite.op ⦋1⦌) t := by
  rw [homotopyEdgeTriangleUpper, homotopySimplex_face]
  have hx : X.δ 0 (X.σ 0 t) = t :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := (0 : Fin 2))) t
  have ht : (Δ[1] : SSet.{u}).δ 0 ((Δ[1] : SSet.{u}).σ 1
      (SSet.yonedaEquiv (𝟙 Δ[1]))) = PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) 1 := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [hx, ht]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app G.h₁ (Opposite.op ⦋1⦌)) t
/-- 概要：上側の三角形の長辺は円柱の対角辺。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopyEdgeTriangleUpper_one {X Y : SSet.{u}}
    (H : X ⊗ Δ[1] ⟶ Y) (t : X _⦋1⦌) :
    Y.δ 1 (homotopyEdgeTriangleUpper H t) =
      H.app (Opposite.op ⦋1⦌) (t, SSet.yonedaEquiv (𝟙 Δ[1])) := by
  rw [homotopyEdgeTriangleUpper, homotopySimplex_face]
  have hx := ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := (0 : Fin 2))) t
  have ht := ConcreteCategory.congr_hom
    ((Δ[1] : SSet.{u}).δ_comp_σ_self (i := (1 : Fin 2))) (SSet.yonedaEquiv (𝟙 Δ[1]))
  rw [show X.δ 1 (X.σ 0 t) = t from hx,
    show (Δ[1] : SSet.{u}).δ 1 ((Δ[1] : SSet.{u}).σ 1 _) = _ from ht]
  rfl
/-- 概要：上側の三角形の最初の辺は始点の垂直辺。
方針：自然性、面と退化の式、端点の条件を使う。
規約：元の一次単体と厳密に一致する。
使われ方：指定円柱から各脚の比較同型を構成する。 -/
lemma homotopyEdgeTriangleUpper_two {X Y : SSet.{u}} {f g : X ⟶ Y}
    (G : SSet.Homotopy f g) (t : X _⦋1⦌) :
    Y.δ 2 (homotopyEdgeTriangleUpper G.h t) =
      (simplicialHomotopyVertexEdge G (X.δ 1 t)).edge := by
  rw [homotopyEdgeTriangleUpper, homotopySimplex_face, homotopyVertexEdge_simplex]
  have hx : X.δ 2 (X.σ 0 t) = X.σ 0 (X.δ 1 t) :=
    ConcreteCategory.congr_hom (X.δ_comp_σ_of_gt (show (0 : Fin 1).castSucc < 1 by decide)) t
  have ht : (Δ[1] : SSet.{u}).δ 2 ((Δ[1] : SSet.{u}).σ 1
      (SSet.yonedaEquiv (𝟙 Δ[1]))) = SSet.yonedaEquiv (𝟙 Δ[1]) :=
    ConcreteCategory.congr_hom ((Δ[1] : SSet.{u}).δ_comp_σ_succ (i := (1 : Fin 2))) _
  rw [hx, ht]

end SerrePositivity.InfinityCategories.F2
