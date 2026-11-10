module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FullSmallPrefixFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndCompactEmbedding

/-!
概要：Ind 模型で小さい全前置図式を固定した compact 余錐の因子化を得る。
方針：元の Ind 包含の compact 保存と filtered 余極限保存を周囲の相対因子化へ渡す。
規約：Ind 模型の全小余極限は仮定しない。
使われ方：共通 κ₀ の表示添字内で行う相対交互構成の各段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：Ind 模型の全 compact 図式を、同じ前置余錐を保って表示の一段へ因子化する。
方針：指定された底の filtered 余極限を包含で保存し、周囲の相対因子化を回収する。
規約：元の前置図式に終頂点を要求しない。
使われ方：長さ κ₀ の相対交互構成の極限前置段。 -/
lemma compactDiagram_factorization_relative_ind
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B J L : SSet.{u}} [Quasicategory B] [Quasicategory J] [Quasicategory L]
    (hJ : IsKappaSmall μ J) (hL : IsKappaSmall μ L)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ Ind.IndInfinity μ B)
    (hQ : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ j))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj J) [Mono i]
    {A : SSet.{u}} [Quasicategory A] [IsKappaFiltered μ A]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder (i ≫ q))
    (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (sliceUnderProjection (i ≫ q)) c))
    (z : JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : A _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = D.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge =
          (Compact.coconeTransportLeg c (ULift.up j)).edge := by
  let j := Ind.indInclusionPresheaf μ B
  have hc' : IsColimitCone (mapJoinCocone (sliceUnderProjection (i ≫ q) ≫ j) c) := by
    have h := Ind.indInclusion_preservesSmallKappaFilteredColimits μ B A
      (D ≫ sliceUnderProjection (i ≫ q)) (mapJoinCocone (sliceUnderProjection (i ≫ q)) c) hc
    exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp h
  exact compactDiagram_factorization_relative_fullSubcomplex hμ hJ hL
    (Ind.IsIndVertex μ B) (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits B) q
    (fun a ↦ indInclusion_preservesCompact μ (q.app _ a) (hQ a)) i D c hc' z hz

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
