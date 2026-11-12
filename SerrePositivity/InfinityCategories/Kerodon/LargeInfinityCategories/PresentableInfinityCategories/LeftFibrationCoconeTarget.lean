module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeTargetExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：left fibration 上の全余錐を、指定した底の終点へ延長する。
方針：底の辺を元の余錐頂点から持ち上げ、その実辺に沿って全余錐を延長する。
規約：元の全図式と底の指定終点を厳密に保持する。
使われ方：compact comma の指定始点付き全余錐の頂点調整。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：底の指定辺に沿って、元の全余錐を同じ図式の全余錐へ延長する。
方針：left fibration の始点指定の辺持ち上げと全余錐の延長を合成する。
規約：辺の可逆性や余錐の普遍性を要求しない。
使われ方：指定 coslice の元の図式を保つ終頂点の調整。 -/
lemma exists_leftFibration_cocone_of_target_edge
    {K E B : SSet.{u}} [Quasicategory E] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {r : K ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) {w : B _⦋0⦌}
    (e : B.Edge (p.app (Opposite.op ⦋0⦌) c.vertex) w) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r, p.app (Opposite.op ⦋0⦌) d.vertex = w := by
  obtain ⟨F, hFs, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source p c.vertex e.toTruncated
  let v := E.δ (0 : Fin 2) (SSet.yonedaEquiv F)
  have hs : E.δ (1 : Fin 2) (SSet.yonedaEquiv F) = c.vertex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hFs, Equiv.apply_symm_apply]
  have ht : p.app (Opposite.op ⦋0⦌) v = w := by
    change p.app _ (E.map (SimplexCategory.δ (0 : Fin 2)).op (SSet.yonedaEquiv F)) = w
    rw [p.naturality_apply, ← SSet.yonedaEquiv_comp, hFp]
    exact (congrArg (fun t ↦ B.map (SimplexCategory.δ (0 : Fin 2)).op t)
      (SSet.yonedaEquiv.apply_symm_apply e.toTruncated.edge)).trans e.tgt_eq
  let f : E.Edge c.vertex v := ⟨SSet.yonedaEquiv F, hs, rfl⟩
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_cocone_of_edge_from_vertex c f
  exact ⟨d, hd ▸ ht⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
