module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma coneSquare_initialVertex {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c) 0 0 = c.vertex := by
  change c.val.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_inv_initialVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
  have h : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have ha := ((stdSimplex.obj₀Equiv.symm (0 : Fin 1)) i).isLt
    have hb := ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).isLt
    omega
  rw [h, ← SSet.yonedaEquiv_comp, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
