module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite

/-!
概要：同型な全図式の間で極限錐の元の頂点を保持して輸送する。
方針：元の反転余錐を同じ頂点で輸送し、slice 反転同型の逆で戻す。
規約：元の全錐と頂点の等号を保持する。
使われ方：全 Hom 係数族の図式比較と表現可能性の移送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：反転した図式の元の余錐から同じ図式の錐へ戻す。
方針：元の slice 反転同型の逆を頂点へ適用する。
規約：反転した全余錐の全射を保持する。
使われ方：指定頂点付きの極限輸送。 -/
def coneOfOppositeCocone {K X : SSet.{u}} (p : K ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.opFunctor.map p)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p :=
  SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).inv.app (Opposite.op ⦋0⦌) d)

/-- 概要：逆反転で構成した錐を反転すると同じ元の余錐へ厳密に戻る。
方針：指定 slice 同型の逆恒等式を零次数へ適用する。
規約：頂点同型だけでなく同じ全余錐の等式である。
使われ方：極限性と頂点の回収。 -/
lemma coneOfOppositeCocone_reverse {K X : SSet.{u}} (p : K ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.opFunctor.map p)) : (coneOfOppositeCocone p d).reverseCocone = d := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).inv_hom_id
  exact h

/-- 概要：逆反転した同じ錐の頂点は元の余錐頂点の反転。
方針：全余錐の回収と既存の頂点反転式を合成する。
規約：元の頂点の厳密な等式を与える。
使われ方：図式同型に沿う極限の頂点保持。 -/
lemma coneOfOppositeCocone_vertex {K X : SSet.{u}} (p : K ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.opFunctor.map p)) :
    (coneOfOppositeCocone p d).vertex = SSet.opObjEquiv d.vertex := by
  have h := (coneOfOppositeCocone p d).reverseCocone_vertex
  rw [coneOfOppositeCocone_reverse] at h
  exact (congrArg SSet.opObjEquiv h).symm

/-- 概要：同型な図式上へ元の極限錐の頂点を保持して輸送できる。
方針：反転余錐を同じ指定頂点で輸送し、同じ反転同型の逆で戻す。
規約：元の任意形状と全錐の普遍性を保持する。
使われ方：全自然な Hom 図式の比較による存在構成。 -/
lemma exists_limitCone_functorIso_sameVertex {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex e.op c.reverseCocone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone c).mp hc)
  refine ⟨coneOfOppositeCocone q d, ?_, ?_⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone _).mpr
    rwa [coneOfOppositeCocone_reverse]
  · rw [coneOfOppositeCocone_vertex, hv, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.reverseCocone_vertex,
      Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
