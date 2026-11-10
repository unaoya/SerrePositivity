module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeSliceCocone
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeLegPointComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactCoconeFactorization

/-!
概要：元の対象上の μ-small compact 図式を元の一つの filtered 表示段へ全余錐として因子化する。
方針：小さい図式の compact 余極限の因子化を、相対 coslice 辺から全 slice 余錐へ戻す。
規約：元の対象と元の指定表示脚を全高次で保持する。
使われ方：fiber の compact comma の全小試験余錐の始端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の対象上の小さい compact 図式は元の表示段へ全余錐を持つ。
方針：compact 図式の全余錐因子化を使い、元の表示脚の上の辺を相対余錐へ展開する。
規約：指定した全 filtered 表示の同じ一段を返す。
使われ方：全 μ-small 試験図式を compact fiber 射の可算回収へ接続する。 -/
lemma compactSliceDiagram_factorization
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E : SSet.{u + 1}} [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex))
    (hr : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((r ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) k)) :
    ∃ (i : I _⦋0⦌) (v : JoinCocone r),
      v.vertex = (coconeSliceDiagram c).app (Opposite.op ⦋0⦌) (ULift.up i) := by
  let a := r ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)
  obtain ⟨ca, hca⟩ := hE K a
  have ht : (sliceDiagramCocone r).vertex = c.vertex := by
    apply SSet.yonedaEquiv.symm.injective
    exact sliceDiagramCocone_point r
  let t : (vertexFiber (sliceUnderProjection a) c.vertex) _⦋0⦌ :=
    ⟨sliceDiagramCocone r, by
      change (sliceDiagramCocone r).vertex = PinchedHom.constant c.vertex 0
      rw [pinchedConstant_zero, ht]⟩
  obtain ⟨i, w, e, he⟩ := Localization.compactDiagram_cocone_factorization hμ hK
    a hr ca hca D c hc t
  let v := relativeSliceCocone r e
  have hv := relativeSliceCocone_vertex_val r e
  change v.vertex.val = (joinStdSimplexIso 0 0).hom ≫
    SSet.yonedaEquiv.symm (e.map (sliceUnderProjection a)).edge at hv
  rw [he] at hv
  refine ⟨i, v, Subtype.ext ?_⟩
  exact hv.trans (coconeTransportLeg_sliceDiagram_val c (ULift.up i))

end SerrePositivity.InfinityCategories.F2.Presentable
