module
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes

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

lemma coneSquare_initialVertex {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : JoinCone p) :
    squareVertex (coneSquare c) 0 0 = c.vertex := by
  change c.val.app (Opposite.op ⦋0⦌) (cospanConeSquareIso.inv.app (Opposite.op ⦋0⦌)
    (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [cospanConeSquareIso_inv_initialVertex, JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
  have h : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have ha := ((stdSimplex.obj₀Equiv.symm (0 : Fin 1)) i).isLt
    have hb := ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).isLt
    omega
  rw [h, ← SSet.yonedaEquiv_comp, Category.id_comp]

end SerrePositivity.InfinityCategories
