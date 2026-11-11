module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.TrivialCosliceEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FactorizationEdgeLift

/-!
概要：自明 Kan 射に沿って、比較辺と全前置図式を保つ因子化を持ち上げる。
方針：指定終点への区間の持ち上げを相対 coslice の端点写像に適用する。
規約：元の比較辺をホモトピーで置き換えない。
使われ方：Ind 模型から元の accessible 圏への因子化の輸送。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：自明 Kan 射は、元の辺を指定された終点へ持ち上げる。
方針：終点の単射に対する持ち上げ性を使う。
規約：始点の持ち上げは出力として与える。
使われ方：相対余錐の因子化辺の厳密な回収。 -/
lemma trivialKan_exists_edge_target {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (t : X _⦋0⦌) {v : Y _⦋0⦌}
    (k : Y.Edge v (p.app _ t)) :
    ∃ w : X _⦋0⦌, ∃ e : X.Edge w t, (e.map p).edge = k.edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (stdSimplex.δ (0 : Fin 2)) inferInstance
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
    {J K E B : SSet.{u}} (q : J ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (D : K ⟶ E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (i : K _⦋0⦌)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) c.vertex) _⦋0⦌)
    {w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q ≫ p)) _⦋0⦌}
    (k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q ≫ p)).Edge w ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp q p).app _ t.val))
    (hk : (k.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q ≫ p))).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).map p).edge) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) (D.app _ i)) _⦋0⦌,
      ∃ e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q).Edge v.val t.val,
        (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap q p
  let a := pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q ≫ p))
  let b := pullback.snd p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q ≫ p))
  have ht : a.app _ (f.app _ t.val) = c.vertex := by
    change (f ≫ a).app _ t.val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst]
    exact t.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  have hb : b.app _ (f.app _ t.val) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp q p).app _ t.val := by
    change (f ≫ b).app _ t.val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_snd]
  let k' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (q ≫ p)).Edge w (b.app _ (f.app _ t.val)) :=
    ⟨k.edge, k.src_eq, k.tgt_eq.trans hb.symm⟩
  obtain ⟨v, l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_factorizationEdge_of_isPullback a b p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (q ≫ p)) (IsPullback.of_hasPullback _ _) D c i
    (f.app _ t.val) ht k' hk
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.cosliceEndpointMap_trivialKanFibration q p
  obtain ⟨z, e, he⟩ := trivialKan_exists_edge_target f t.val l
  have ha : (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge := by
    calc
      _ = (e.map (f ≫ a)).edge := congrArg (fun g ↦ g.app _ e.edge)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst q p).symm
      _ = (l.map a).edge := congrArg (fun z ↦ a.app _ z) he
      _ = _ := hl
  have hz : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q).app _ z = D.app _ i := by
    calc
      _ = E.δ 1 (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)).edge :=
        (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)).src_eq.symm
      _ = E.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge := congrArg (E.δ 1) ha
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).src_eq
  exact ⟨⟨z, hz.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩, e, ha⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
