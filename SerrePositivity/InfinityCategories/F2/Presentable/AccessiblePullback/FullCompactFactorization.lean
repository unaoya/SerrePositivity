module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FactorizationEdgeLift
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactCoconeFactorization

/-!
概要：全部分圏の全 compact 前置図式を、周囲の余完備な圏で因子化して厳密に回収する。
方針：周囲の compact 余極限を使う因子化の辺を、元の全 coslice の実引き戻しへ戻す。
規約：元の全部分圏で前置図式の余極限が存在するとは仮定しない。
使われ方：一般 accessible 圏の相対交互構成の全前置図式を保つ延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：全部分圏の全 compact 図式の指定余錐は、同じ filtered 表示の一段へ因子化する。
方針：周囲で全余錐を因子化し、その実辺を元の底の余錐脚に沿って引き戻す。
規約：全小余極限は周囲だけに要求し、元の全余錐と比較辺を保持する。
使われ方：Ind 模型内の相対構成での μ-small 前置図式の固定。 -/
lemma compactDiagram_factorization_of_fullSubcomplex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {X : SSet.{u + 1}} [Quasicategory X] (P : X _⦋0⦌ → Prop) (hX : HasSmallColimits X)
    {A : SSet.{u}} [Quasicategory A] (hA : IsKappaSmall μ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (fullSubcomplexOnVertices X P : SSet.{u + 1}))
    (hq : ∀ a, Compact.IsKappaCompact.{u, u + 1} μ
      ((q ≫ (fullSubcomplexOnVertices X P).ι).app _ a))
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered μ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (fullSubcomplexOnVertices X P : SSet.{u + 1}))
    (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices X P).ι c))
    (t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌) :
    ∃ i : K _⦋0⦌,
      ∃ w : (vertexFiber (sliceUnderProjection q) (D.app _ (ULift.up i))) _⦋0⦌,
      ∃ e : (sliceUnder q).Edge w.val t.val,
        (e.map (sliceUnderProjection q)).edge = (Compact.coconeTransportLeg c (ULift.up i)).edge := by
  let j := (fullSubcomplexOnVertices X P).ι
  let s := Compact.fullSliceUnder_isPullback P q
  let c' := mapJoinCocone j c
  let t' := (sliceUnderPostcomp q j).app (Opposite.op ⦋0⦌) t.val
  have ht : (sliceUnderProjection q).app (Opposite.op ⦋0⦌) t.val = c.vertex :=
    t.property.trans (pinchedConstant_zero _)
  have ht' : (sliceUnderProjection (q ≫ j)).app (Opposite.op ⦋0⦌) t' = c'.vertex := by
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) t.val) s.w
    change j.app _ ((sliceUnderProjection q).app _ t.val) =
      (sliceUnderProjection (q ≫ j)).app _ t' at h
    rw [ht] at h
    exact h.symm.trans (Ind.mapJoinCocone_vertex j c).symm
  let tf : (vertexFiber (sliceUnderProjection (q ≫ j)) c'.vertex) _⦋0⦌ :=
    ⟨t', ht'.trans (pinchedConstant_zero _).symm⟩
  obtain ⟨cq, hcq⟩ := hX A (q ≫ j)
  obtain ⟨i, w, k, hk⟩ := Localization.compactDiagram_cocone_factorization hμ hA
    (q ≫ j) hq cq hcq (D ≫ j) c' hc tf
  have hk' : (k.map (sliceUnderProjection (q ≫ j))).edge =
      ((Compact.coconeTransportLeg c (ULift.up i)).map j).edge :=
    hk.trans (Compact.coconeTransportLeg_post_edge j c (ULift.up i))
  obtain ⟨v, e, he⟩ := exists_factorizationEdge_of_isPullback
    (sliceUnderProjection q) (sliceUnderPostcomp q j) j (sliceUnderProjection (q ≫ j))
    s D c (ULift.up i) t.val ht k hk'
  exact ⟨i, v, e, he⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
