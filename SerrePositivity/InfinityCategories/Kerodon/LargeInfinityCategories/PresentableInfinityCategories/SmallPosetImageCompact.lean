module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetColimitGenerators
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor

/-!
概要：小さい poset 余極限で得る生成候補の関手像も、共通濃度で compact にする。
方針：元の指定余錐の保存性と標的内の小さい余極限の compact 性を合わせる。
規約：関手が全 compact 対象を保存することは仮定しない。
使われ方：引き戻しの両成分の compact 生成族と、その標的像の濃度調整。

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
namespace SmallPosetDiagramCode

/-- 概要：小さい部分余極限の像は、元の生成族の像と同じ μ に関して compact。
方針：同じ κ-filtered 余錐を元の関手で送り、標的内の μ-small poset 余極限を評価する。
規約：κ-filtered 保存と元の生成族の像の compact 性だけを要求する。
使われ方：像も compact な小さい生成候補族の構成。 -/
lemma image_vertex_isMuCompact
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) {A : SSet.{u}}
    {C D : SSet.{u + 1}} [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (G : C ⟶ D) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (hi : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ (i.app _ (ULift.up a))))
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ (q.vertex hC i)) := by
  have := q.nerve_isKappaFiltered
  have hc := hG (nerve q.Index) (q.realizedDiagram i) (q.colimitCone hC i)
    (q.colimitCone_isColimit hC i)
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isMuCompact_smallPosetColimit h q.Index q.small
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (q.colimitCone hC i)) hc (fun k ↦ ?_)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] at hx
    exact hx
  · rcases k with ⟨k⟩
    exact hi (q.map.app _ k)

end SmallPosetDiagramCode
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
