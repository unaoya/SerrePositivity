module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinBaseFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalProjection

/-!
概要：元の相対 join の同じ頂点 fiber の余錐包含の、元の通常 join と底への射影を計算する。
方針：構成済みの同じ fiber 同型を両射影で読み、底変換同型の往復を消去する。
規約：元の fiber 包含を固定。使われ方：元の全単位の係数制限との厳密な prism 比較。

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

/-- 元の fiber の通常余錐を、同じ相対 join の元の fiber へ含める。 -/
def relativeJoinFiberEmbedding : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) (Δ[0] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso p c).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) c

/-- 同じ fiber 包含の通常 join 成分は、元の fiber 包含と同じ指定頂点の join。 -/
lemma relativeJoinFiberEmbedding_fst :
    relativeJoinFiberEmbedding p c ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c) (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C) := by
  rw [relativeJoinFiberEmbedding, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinBaseFiberIso_hom_ι]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_fst, IsIso.inv_hom_id_assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, IsPullback.isoPullback_hom_fst]

/-- 同じ元の fiber 包含の底は、同じ指定頂点に定値。 -/
lemma relativeJoinFiberEmbedding_base :
    relativeJoinFiberEmbedding p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) = SSet.const c := by
  rw [relativeJoinFiberEmbedding, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 元の相対 join の区間射影は、元の通常 join 成分の区間射影である。 -/
lemma relativeJoinProjection_eq_fst_interval :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection p (𝟙 C) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection K C := by
  have h := congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection C C)
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p (𝟙 C)) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C))
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection] using h.symm

/-- 同じ fiber 包含の区間付き底は、元の通常余錐の区間と同じ指定頂点の組。 -/
lemma relativeJoinFiberEmbedding_snd :
    relativeJoinFiberEmbedding p c ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) Δ[0]) (SSet.const c) := by
  apply CartesianMonoidalCategory.hom_ext
  · change relativeJoinFiberEmbedding p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection p (𝟙 C) = _
    rw [relativeJoinProjection_eq_fst_interval, ← Category.assoc,
      relativeJoinFiberEmbedding_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality, lift_fst]
  · exact relativeJoinFiberEmbedding_base p c

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
