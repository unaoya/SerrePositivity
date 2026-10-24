module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinBaseFiber
public import SerrePositivity.InfinityCategories.F1.Joins.JoinIntervalProjection

/-!
概要：元の相対 join の同じ頂点 fiber の余錐包含の、元の通常 join と底への射影を計算する。
方針：構成済みの同じ fiber 同型を両射影で読み、底変換同型の往復を消去する。
規約：元の fiber 包含を固定。使われ方：元の全単位の係数制限との厳密な prism 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌)

/-- 元の fiber の通常余錐を、同じ相対 join の元の fiber へ含める。 -/
def relativeJoinFiberEmbedding : join (vertexFiber p c) (Δ[0] : SSet.{u}) ⟶
    relativeJoin p (𝟙 C) :=
  (kanRelativeJoinBaseFiberIso p c).hom ≫
    vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c

/-- 同じ fiber 包含の通常 join 成分は、元の fiber 包含と同じ指定頂点の join。 -/
lemma relativeJoinFiberEmbedding_fst :
    relativeJoinFiberEmbedding p c ≫ pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C) =
      joinMap (vertexFiberι p c) (SSet.const c : (Δ[0] : SSet.{u}) ⟶ C) := by
  rw [relativeJoinFiberEmbedding, kanRelativeJoinBaseFiberIso_hom_ι]
  simp only [Category.assoc, relativeJoinPullbackMap_fst, IsIso.inv_hom_id_assoc]
  rw [← joinMap_comp, Category.id_comp, IsPullback.isoPullback_hom_fst]

/-- 同じ元の fiber 包含の底は、同じ指定頂点に定値。 -/
lemma relativeJoinFiberEmbedding_base :
    relativeJoinFiberEmbedding p c ≫ relativeJoinBaseProjection p (𝟙 C) = SSet.const c := by
  rw [relativeJoinFiberEmbedding, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 元の相対 join の区間射影は、元の通常 join 成分の区間射影である。 -/
lemma relativeJoinProjection_eq_fst_interval :
    relativeJoinProjection p (𝟙 C) =
      pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C) ≫ joinIntervalProjection K C := by
  have h := congrArg (fun f ↦ f ≫ joinIntervalProjection C C)
    (pullback.condition (f := joinMap p (𝟙 C)) (g := joinDiagonal C))
  simpa only [Category.assoc, joinIntervalProjection_naturality,
    joinDiagonal_joinIntervalProjection, relativeJoinProjection] using h.symm

/-- 同じ fiber 包含の区間付き底は、元の通常余錐の区間と同じ指定頂点の組。 -/
lemma relativeJoinFiberEmbedding_snd :
    relativeJoinFiberEmbedding p c ≫ pullback.snd (joinMap p (𝟙 C)) (joinDiagonal C) =
      lift (joinIntervalProjection (vertexFiber p c) Δ[0]) (SSet.const c) := by
  apply CartesianMonoidalCategory.hom_ext
  · change relativeJoinFiberEmbedding p c ≫ relativeJoinProjection p (𝟙 C) = _
    rw [relativeJoinProjection_eq_fst_interval, ← Category.assoc,
      relativeJoinFiberEmbedding_fst, joinIntervalProjection_naturality, lift_fst]
  · exact relativeJoinFiberEmbedding_base p c

end SerrePositivity.InfinityCategories.F2.Ind
