module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationTower
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexPrefix

/-!
概要：全交互段の増大余錐を、固定頂点の slice 内の全図式として表示する。
方針：元の全増大余錐の偶数制限から標的固定を回収し、全 curry を使う。
規約：元の指定余錐頂点を保ち、全前置面の整合を保持する。
使われ方：固定標的上の全可算交互図式の貼り合わせ。

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

variable {I : SSet.{u}} {B : SSet.{u + 1}}
  {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D} {n : ℕ}

/-- 概要：全交互段の増大余錐の標的は元の指定余錐頂点そのもの。
方針：偶数増大余錐の全等式を右因子へ制限する。
規約：元の頂点の Yoneda 表示との厳密な等式。
使われ方：交互段を同じ固定標的の slice へ送る。 -/
lemma AlternatingPresentationStage.augmentation_right (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[2 * n] Δ[0] ≫ s.augmentation.val = SSet.yonedaEquiv.symm c.vertex := by
  have h := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u + 1}) Δ[0] ≫ f) s.augmentation_eq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0] ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)) (𝟙 Δ[0]) ≫ s.augmentation.val) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index) (𝟙 Δ[0]) ≫ c.val) at h
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, Equiv.symm_apply_apply]
  exact h

/-- 概要：全交互段を元の指定余錐頂点上の slice 内の図式にする。
方針：全増大余錐を右固定条件に沿って curry する。
規約：同じ元の余錐頂点を使う。
使われ方：増大余錐を含む可算貼り合わせ。 -/
def AlternatingPresentationStage.sliceDiagram (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    (Δ[2 * n] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry s.augmentation.val s.augmentation_right

/-- 概要：固定標的の slice 図式の全展開は元の増大余錐そのもの。
方針：curry と uncurry の厳密な逆関係。
規約：全射の等式。
使われ方：slice 内の全図式を元の増大余錐へ戻す。 -/
lemma AlternatingPresentationStage.sliceDiagram_uncurry (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s.sliceDiagram = s.augmentation.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry _ _

/-- 概要：固定標的の slice 図式の射影は元の全交互図式。
方針：curry の射影公式と元の余錐の固定条件を使う。
規約：全射の等式。
使われ方：元の標的圏内の交互図式の回収。 -/
lemma AlternatingPresentationStage.sliceDiagram_projection
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    s.sliceDiagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) = s.diagram := by
  rw [sliceDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection]
  exact s.augmentation.property

/-- 概要：後続段の固定標的 slice 図式は元の全前置図式を延長する。
方針：全 uncurry の単射性と増大余錐の全固定条件を使う。
規約：全高次成分を厳密に保持する。
使われ方：固定標的 slice 内の可算貼り合わせ。 -/
lemma AlternatingPresentationSuccessor.next_sliceDiagram_prefix
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationSuccessor s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix (by omega : 2 * n ≤ 2 * (n + 1)) ≫ t.next.sliceDiagram = s.sliceDiagram := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (SSet.yonedaEquiv.symm c.vertex)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, AlternatingPresentationStage.sliceDiagram_uncurry,
    AlternatingPresentationStage.sliceDiagram_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix_alternating]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtensionCocone_old _ t.triangle

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
