module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.YonedaIdentityPointTransports

/-!
概要：二方向の恒等点輸送の共通の底を、元の表現可能前層の値へ正規化する。
方針：元の反変辺の終点と、同じ前層の面写像の自然性を使う。
規約：共通の pointed 終点はそのまま保持し、底の表示だけを厳密に照合する。
使われ方：Yoneda 評価の第一変数の自然性を同じ元の値の fiber 内で扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の共通 pointed 終点の底は、元の表現可能前層 y の x での実際の値。 -/
lemma yonedaIdentityCommonFiber_base {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedEdgeVertex f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm
            (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
    (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))
  have hc : ((SSet.uliftFunctor.{u + 1, u}).obj C.op).δ 0
      (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) =
    ULift.up (SSet.opObjEquiv.symm
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) := by
    change ULift.up (C.op.δ 0 (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) = _
    rw [op_δ, Equiv.apply_symm_apply]
    have h : C.δ 1 (SSet.yonedaEquiv f) =
        f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) := by
      have hδ : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          SimplexCategory.δ (1 : Fin 2) := by decide
      have h := SSet.yonedaEquiv_symm_app (SSet.yonedaEquiv f)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
      simpa only [Equiv.symm_apply_apply, hδ, ← SimplicialObject.δ_def] using h.symm
    change ULift.up (SSet.opObjEquiv.symm (C.δ 1 (SSet.yonedaEquiv f))) = _
    rw [h]
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge f).tgt_eq
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge_edge] at h
  have hn := SSet.δ_naturality_apply F (0 : Fin 2)
    (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f)))
  rw [hc] at hn
  exact h.symm.trans hn.symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
