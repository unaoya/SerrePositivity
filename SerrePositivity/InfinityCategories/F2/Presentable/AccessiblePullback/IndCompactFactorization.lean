module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FullCompactFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndCompactEmbedding

/-!
概要：Ind 模型の全 compact 前置図式を filtered 表示の一段へ因子化する。
方針：前層内の compact 保存と filtered 余極限保存を全余錐の因子化へ渡す。
規約：Ind 模型自身には全小余極限を仮定しない。
使われ方：長い相対交互構成の極限段で、全前置図式を保つ延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：Ind 模型の小さい compact 図式の余錐は、指定脚に沿って一段へ因子化する。
方針：全 Ind 包含による compact 保存と余錐保存を周囲の因子化へ接続する。
規約：元の全前置図式、最終余錐、底の比較辺を厳密に保持する。
使われ方：一般 accessible 圏への同値輸送前の因子化。 -/
lemma compactDiagram_factorization_ind
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A]
    {J : SSet.{u}} [Quasicategory J] (hJ : IsKappaSmall μ J)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ Ind.IndInfinity μ A)
    (hq : ∀ a, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ a))
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered μ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Ind.IndInfinity μ A)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌) :
    ∃ i : K _⦋0⦌,
      ∃ w : (vertexFiber (sliceUnderProjection q) (D.app _ (ULift.up i))) _⦋0⦌,
      ∃ e : (sliceUnder q).Edge w.val t.val,
        (e.map (sliceUnderProjection q)).edge =
          (Compact.coconeTransportLeg c (ULift.up i)).edge := by
  exact compactDiagram_factorization_of_fullSubcomplex hμ
    (Ind.IsIndVertex μ A) (presheaf_hasSmallColimits A) hJ q
    (fun a ↦ indInclusion_preservesCompact μ (q.app _ a) (hq a)) D c
    (Ind.indInclusion_preservesSmallKappaFilteredColimits μ A K D c hc) t

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
