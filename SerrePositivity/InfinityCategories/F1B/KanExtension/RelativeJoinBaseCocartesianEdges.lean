module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinMapCocartesianEdges
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianProductProjection
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FinalHornPullbackExtension
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinBaseFiber

/-!
概要：相対 join の両端の包含による底上の cocartesian 辺の構成。
方針：joinMap の辺を prism への pullback に持ち上げ、底の第二射影に合成する。
規約：左端は元の射の cocartesian 辺、右端は任意の底の辺を使う。
使われ方：相対 join の底への cocartesian 輸送と左包含の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の左包含は元の射の cocartesian 辺を底上の cocartesian 辺へ送る。
方針：joinMap の辺の底変換と、端点零での prism の輸送を合成する。
規約：元の射全体の fibration 性は不要。
使われ方：余錐の図式から元の図式への制限の輸送との両立。 -/
lemma kanRelativeJoinInl_base_isCocartesianEdge {K C : SSet.{u}} (p : K ⟶ C)
    (e : K _⦋1⦌) (he : IsCocartesianEdge p e) :
    IsCocartesianEdge (relativeJoinBaseProjection p (𝟙 C))
      ((relativeJoinInl p (𝟙 C)).app (Opposite.op ⦋1⦌) e) := by
  let q := pullback.snd (joinMap p (𝟙 C)) (joinDiagonal C)
  let s := (relativeJoinInl p (𝟙 C)).app (Opposite.op ⦋1⦌) e
  have hf : (pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C)).app _ s =
      (joinInl K C).app (Opposite.op ⦋1⦌) e :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e) (relativeJoinInl_fst p (𝟙 C))
  have hs : IsCocartesianEdge q s :=
    SerrePositivity.InfinityCategories.isCocartesianEdge_isPullback (IsPullback.of_hasPullback _ _) s (by
      rw [hf]
      exact SerrePositivity.InfinityCategories.F1B.joinMap_right_id_inl_isCocartesianEdge p e he)
  apply hs.comp
  have hq : q.app (Opposite.op ⦋1⦌) s =
      (prismEndpoint 0 C).app (Opposite.op ⦋1⦌) (p.app (Opposite.op ⦋1⦌) e) :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e)
      (pullback.lift_snd (joinInl K C) (p ≫ prismEndpoint 0 C) _)
  rw [hq]
  exact SerrePositivity.InfinityCategories.F1B.prismEndpoint_isCocartesianEdge 0 _

/-- 概要：相対 join の右包含はすべての底の辺を底上の cocartesian 辺へ送る。
方針：右恒等の joinMap と端点一での prism の輸送を合成する。
規約：p の充填性や C の quasicategory 性は不要。
使われ方：相対 join の右端を始点とする底の辺の持ち上げ。 -/
lemma kanRelativeJoinInr_base_isCocartesianEdge {K C : SSet.{u}} (p : K ⟶ C)
    (e : C _⦋1⦌) :
    IsCocartesianEdge (relativeJoinBaseProjection p (𝟙 C))
      ((relativeJoinInr p (𝟙 C)).app (Opposite.op ⦋1⦌) e) := by
  let q := pullback.snd (joinMap p (𝟙 C)) (joinDiagonal C)
  let s := (relativeJoinInr p (𝟙 C)).app (Opposite.op ⦋1⦌) e
  have hf : (pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C)).app _ s =
      (joinInr K C).app (Opposite.op ⦋1⦌) e :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e) (relativeJoinInr_fst p (𝟙 C))
  have hs : IsCocartesianEdge q s :=
    SerrePositivity.InfinityCategories.isCocartesianEdge_isPullback (IsPullback.of_hasPullback _ _) s (by
      rw [hf]
      exact SerrePositivity.InfinityCategories.F1B.joinMap_right_id_inr_isCocartesianEdge p e)
  apply hs.comp
  have hq : q.app (Opposite.op ⦋1⦌) s =
      (prismEndpoint 1 C).app (Opposite.op ⦋1⦌) e :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e)
      (pullback.lift_snd (joinInr K C) ((𝟙 C) ≫ prismEndpoint 1 C) _)
  rw [hq]
  exact SerrePositivity.InfinityCategories.F1B.prismEndpoint_isCocartesianEdge 1 _

end SerrePositivity.InfinityCategories.F1B
