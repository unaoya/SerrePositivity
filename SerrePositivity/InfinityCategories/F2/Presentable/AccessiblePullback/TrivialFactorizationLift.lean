module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.TrivialCosliceEndpoint
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FactorizationEdgeLift

/-!
概要：自明 Kan 射に沿って、比較辺と全前置図式を保つ因子化を持ち上げる。
方針：指定終点への区間の持ち上げを相対 coslice の端点写像に適用する。
規約：元の比較辺をホモトピーで置き換えない。
使われ方：Ind 模型から元の accessible 圏への因子化の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：自明 Kan 射は、元の辺を指定された終点へ持ち上げる。
方針：終点の単射に対する持ち上げ性を使う。
規約：始点の持ち上げは出力として与える。
使われ方：相対余錐の因子化辺の厳密な回収。 -/
lemma trivialKan_exists_edge_target {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] (t : X _⦋0⦌) {v : Y _⦋0⦌}
    (k : Y.Edge v (p.app _ t)) :
    ∃ w : X _⦋0⦌, ∃ e : X.Edge w t, (e.map p).edge = k.edge := by
  have := TrivialKanFibration.mem (p := p) (stdSimplex.δ (0 : Fin 2)) inferInstance
  have hs : CommSq (SSet.yonedaEquiv.symm t) (stdSimplex.δ (0 : Fin 2)) p
      (SSet.yonedaEquiv.symm k.edge) := by
    constructor
    rw [SSet.yonedaEquiv_symm_comp, k.δ_zero_yonedaEquiv_symm]
  let F := hs.lift
  let w := SSet.yonedaEquiv (stdSimplex.δ 1 ≫ F)
  let e : X.Edge w t := ⟨SSet.yonedaEquiv F, by
    change X.δ 1 (SSet.yonedaEquiv F) = w
    rw [← stdSimplex.yonedaEquiv_δ_comp], by
    change X.δ 0 (SSet.yonedaEquiv F) = t
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs.fac_left, Equiv.apply_symm_apply]⟩
  refine ⟨w, e, ?_⟩
  change p.app _ (SSet.yonedaEquiv F) = k.edge
  rw [← SSet.yonedaEquiv_comp, hs.fac_right, Equiv.apply_symm_apply]

/-- 概要：全余錐の因子化辺を、同じ余錐脚を固定して自明 Kan 射に沿って回収する。
方針：底の脚と因子化辺を実引き戻しに貼り、相対端点写像を持ち上げる。
規約：元の全前置図式と最終余錐をそのまま保持する。
使われ方：同値の共通解像を経由した全 compact 前置図式の因子化。 -/
lemma exists_factorizationEdge_of_trivialKan
    {J K E B : SSet.{u}} (q : J ⟶ E) (p : E ⟶ B) [TrivialKanFibration p]
    (D : K ⟶ E) (c : JoinCocone D) (i : K _⦋0⦌)
    (t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌)
    {w : (sliceUnder (q ≫ p)) _⦋0⦌}
    (k : (sliceUnder (q ≫ p)).Edge w ((sliceUnderPostcomp q p).app _ t.val))
    (hk : (k.map (sliceUnderProjection (q ≫ p))).edge =
      ((Compact.coconeTransportLeg c i).map p).edge) :
    ∃ v : (vertexFiber (sliceUnderProjection q) (D.app _ i)) _⦋0⦌,
      ∃ e : (sliceUnder q).Edge v.val t.val,
        (e.map (sliceUnderProjection q)).edge = (Compact.coconeTransportLeg c i).edge := by
  let f := cosliceEndpointMap q p
  let a := pullback.fst p (sliceUnderProjection (q ≫ p))
  let b := pullback.snd p (sliceUnderProjection (q ≫ p))
  have ht : a.app _ (f.app _ t.val) = c.vertex := by
    change (f ≫ a).app _ t.val = _
    rw [cosliceEndpointMap_fst]
    exact t.property.trans (pinchedConstant_zero _)
  have hb : b.app _ (f.app _ t.val) = (sliceUnderPostcomp q p).app _ t.val := by
    change (f ≫ b).app _ t.val = _
    rw [cosliceEndpointMap_snd]
  let k' : (sliceUnder (q ≫ p)).Edge w (b.app _ (f.app _ t.val)) :=
    ⟨k.edge, k.src_eq, k.tgt_eq.trans hb.symm⟩
  obtain ⟨v, l, hl⟩ := exists_factorizationEdge_of_isPullback a b p
    (sliceUnderProjection (q ≫ p)) (IsPullback.of_hasPullback _ _) D c i
    (f.app _ t.val) ht k' hk
  have : TrivialKanFibration f := cosliceEndpointMap_trivialKanFibration q p
  obtain ⟨z, e, he⟩ := trivialKan_exists_edge_target f t.val l
  have ha : (e.map (sliceUnderProjection q)).edge = (Compact.coconeTransportLeg c i).edge := by
    calc
      _ = (e.map (f ≫ a)).edge := congrArg (fun g ↦ g.app _ e.edge)
        (cosliceEndpointMap_fst q p).symm
      _ = (l.map a).edge := congrArg (fun z ↦ a.app _ z) he
      _ = _ := hl
  have hz : (sliceUnderProjection q).app _ z = D.app _ i := by
    calc
      _ = E.δ 1 (e.map (sliceUnderProjection q)).edge :=
        (e.map (sliceUnderProjection q)).src_eq.symm
      _ = E.δ 1 (Compact.coconeTransportLeg c i).edge := congrArg (E.δ 1) ha
      _ = _ := (Compact.coconeTransportLeg c i).src_eq
  exact ⟨⟨z, hz.trans (pinchedConstant_zero _).symm⟩, e, ha⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
