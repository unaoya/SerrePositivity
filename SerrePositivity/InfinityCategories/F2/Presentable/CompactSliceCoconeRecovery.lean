module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSliceDiagramFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeTargetExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeAlternatingCompactSource

/-!
概要：元の対象上の任意の μ-small compact 図式の全余錐を、像が恒等錐と同型な compact 始域に取る。
方針：元の一表示段へ全余錐を因子化し、初期段を保持する可算交互終段へ延長する。
規約：第二脚の保存性も全図式の因子化入力も要求しない。
使われ方：固定標的 fiber の compact comma の全小試験余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の対象上の小さい compact 図式に、像が恒等錐と同型な compact 頂点の全余錐を構成する。
方針：全 μ-small 図式の表示段への因子化と元の表示段からの可算 compact 回収を合成する。
規約：元の全図式と指定対象を固定する。
使われ方：fiber の μ-small 試験余錐の第一成分。 -/
lemma exists_compactSliceCocone_image_identity_of_filteredPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : HasSmallColimits E) (hB : HasSmallColimits B)
    (p : E ⟶ B) (hp : PreservesSmallColimits p)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ E)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up j)))
    (hpD : ∀ j : I _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ ((D ≫ p).app _ (ULift.up j)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ (mapJoinCocone p c).vertex)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex))
    (hr : ∀ k, Compact.IsKappaCompact.{u, u + 1} μ
      ((r ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) k)) :
    ∃ d : JoinCocone r,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)).app (Opposite.op ⦋0⦌) d.vertex) ∧
      Nonempty (VertexIso ((coconeSliceImageMap c p).app (Opposite.op ⦋0⦌) d.vertex)
        (sliceIdentityCone (mapJoinCocone p c).vertex)) := by
  obtain ⟨i, ci, hci⟩ := compactSliceDiagram_factorization hμ hK hE D c hc r hr
  obtain ⟨v, hvcompact, he, ⟨leg⟩⟩ :=
    exists_compactSliceSource_image_identity_initial_of_filteredPresentation
      hμ hE hB p hp D c hc hD hpD hv i
  rw [← hci] at leg
  obtain ⟨d, hd⟩ := exists_cocone_of_edge_from_vertex ci leg
  refine ⟨d, ?_, ?_⟩
  · rw [hd]
    exact hvcompact
  · rw [hd]
    exact he

end SerrePositivity.InfinityCategories.F2.Presentable
