module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeJoinFiberEmbedding
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalEndpointPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFiberCocone

/-!
概要：元の相対 join の fiber 余錐の頂点は、元の右制限の同じ指定頂点そのもの。
方針：同じ fiber 包含の右端を両射影で比較し、元の native 余錐の頂点へ評価する。
規約：元の fiber 同型と指定頂点を固定。使われ方：係数単位との端点固定比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌)

/-- 同じ元の fiber 余錐包含の右端は、元の指定底頂点の右包含そのもの。 -/
lemma relativeJoinFiberEmbedding_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeJoinFiberEmbedding p c =
      (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeJoinFiberEmbedding_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeJoinFiberEmbedding_snd,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, pullback.lift_snd]
    rw [comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inr]
    rfl

/-- 元の相対 join 図式から取り出した同じ native fiber 余錐の頂点の厳密な値。 -/
lemma relativeJoinFiberCocone_vertex {X : SSet.{u}}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c H).vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H).app (Opposite.op ⦋0⦌) c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeJoinFiberEmbedding p c ≫ H)) = _
  rw [← Category.assoc, relativeJoinFiberEmbedding_inr, Category.assoc,
    SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
