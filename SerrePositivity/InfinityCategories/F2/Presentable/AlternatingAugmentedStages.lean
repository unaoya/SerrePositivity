module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingPresentationTower
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialSimplexPrefix

/-!
概要：全交互段の増大余錐を、固定頂点の slice 内の全図式として表示する。
方針：元の全増大余錐の偶数制限から標的固定を回収し、全 curry を使う。
規約：元の指定余錐頂点を保ち、全前置面の整合を保持する。
使われ方：固定標的上の全可算交互図式の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I : SSet.{u}} {B : SSet.{u + 1}}
  {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : JoinCocone D} {n : ℕ}

/-- 概要：全交互段の増大余錐の標的は元の指定余錐頂点そのもの。
方針：偶数増大余錐の全等式を右因子へ制限する。
規約：元の頂点の Yoneda 表示との厳密な等式。
使われ方：交互段を同じ固定標的の slice へ送る。 -/
lemma AlternatingPresentationStage.augmentation_right (s : AlternatingPresentationStage D c n) :
    joinInr Δ[2 * n] Δ[0] ≫ s.augmentation.val = SSet.yonedaEquiv.symm c.vertex := by
  have h := congrArg (fun f ↦ joinInr (Δ[n] : SSet.{u + 1}) Δ[0] ≫ f) s.augmentation_eq
  change joinInr Δ[n] Δ[0] ≫
    (joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]) ≫ s.augmentation.val) =
    joinInr Δ[n] Δ[0] ≫ (joinMap (finiteStageBaseMap s.index) (𝟙 Δ[0]) ≫ c.val) at h
  simp only [← Category.assoc, joinInr_joinMap, Category.id_comp] at h
  rw [JoinCocone.vertex_eq, Equiv.symm_apply_apply]
  exact h

/-- 概要：全交互段を元の指定余錐頂点上の slice 内の図式にする。
方針：全増大余錐を右固定条件に沿って curry する。
規約：同じ元の余錐頂点を使う。
使われ方：増大余錐を含む可算貼り合わせ。 -/
def AlternatingPresentationStage.sliceDiagram (s : AlternatingPresentationStage D c n) :
    (Δ[2 * n] : SSet.{u + 1}) ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex) :=
  sliceOverCurry s.augmentation.val s.augmentation_right

/-- 概要：固定標的の slice 図式の全展開は元の増大余錐そのもの。
方針：curry と uncurry の厳密な逆関係。
規約：全射の等式。
使われ方：slice 内の全図式を元の増大余錐へ戻す。 -/
lemma AlternatingPresentationStage.sliceDiagram_uncurry (s : AlternatingPresentationStage D c n) :
    sliceOverUncurry s.sliceDiagram = s.augmentation.val :=
  sliceOverUncurry_curry _ _

/-- 概要：固定標的の slice 図式の射影は元の全交互図式。
方針：curry の射影公式と元の余錐の固定条件を使う。
規約：全射の等式。
使われ方：元の標的圏内の交互図式の回収。 -/
lemma AlternatingPresentationStage.sliceDiagram_projection
    (s : AlternatingPresentationStage D c n) :
    s.sliceDiagram ≫ sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) = s.diagram := by
  rw [sliceDiagram, sliceOverCurry_projection]
  exact s.augmentation.property

/-- 概要：後続段の固定標的 slice 図式は元の全前置図式を延長する。
方針：全 uncurry の単射性と増大余錐の全固定条件を使う。
規約：全高次成分を厳密に保持する。
使われ方：固定標的 slice 内の可算貼り合わせ。 -/
lemma AlternatingPresentationSuccessor.next_sliceDiagram_prefix
    {s : AlternatingPresentationStage D c n} (t : AlternatingPresentationSuccessor s) :
    simplexPrefix (by omega : 2 * n ≤ 2 * (n + 1)) ≫ t.next.sliceDiagram = s.sliceDiagram := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm c.vertex)
  rw [sliceOverUncurry_precomp, AlternatingPresentationStage.sliceDiagram_uncurry,
    AlternatingPresentationStage.sliceDiagram_uncurry, simplexPrefix_alternating]
  exact standardAlternatingExtensionCocone_old _ t.triangle

end SerrePositivity.InfinityCategories.F2.Presentable
