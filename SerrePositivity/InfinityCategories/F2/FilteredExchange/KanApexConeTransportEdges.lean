module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpecifiedApexConeRestrictions
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanNativeConeLeg

/-!
概要：Kan 射の元の比較辺に沿う錐輸送の頂点・図式の辺を一様に読み戻す。
方針：指定円柱の二制限を各頂点で評価する。
規約：元の射と全一単体を保持。使われ方：coherent 余極限後の錐の脚を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {D : I ⥤ KanObject.{u}}
  (d : JoinCone (kanDiagramCoherentNerve D))
  {K L : KanObject.{u}} (a : K ⟶ L) {v : SpaceInfinity.{u} _⦋0⦌}
  (t : SpecifiedApexLimitConeTransport d (SSet.yonedaEquiv.symm v)
    (edgeApexPrism (coherentNerveEdge a)))

/-- 輸送した錐の頂点は元の Kan 射の始域の頂点そのもの。 -/
lemma kanApexConeTransport_vertex (hv : v = coherentNerveVertex K) :
    t.cone.vertex = coherentNerveVertex K := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ t.cone.val) = _
  rw [t.apex_eq, SSet.yonedaEquiv.apply_symm_apply]
  exact hv

/-- 全錐輸送の頂点辺は元の Kan 射の coherent な辺の全一単体。 -/
lemma kanApexConeTransport_apexEdge :
    (coneHomotopyApexEdge t.homotopy).edge = (coherentNerveEdge a).edge := by
  have h := homotopyVertexEdge_prism t.homotopy (joinInl _ _)
    (edgeApexPrism (coherentNerveEdge a)) t.apex (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id (coherentNerveEdge a).edge)

/-- 全錐輸送の図式の辺は元の図式の値の定値な一単体。 -/
lemma kanApexConeTransport_diagramEdge
    (i : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    (coneHomotopyDiagramEdge t.homotopy i).edge =
      PinchedHom.constant ((kanDiagramCoherentNerve D).app
        (Opposite.op ⦋0⦌) i) 1 :=
  homotopyVertexEdge_constant t.homotopy (joinInr _ _) _ t.diagram i

end SerrePositivity.InfinityCategories.F2
