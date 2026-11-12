module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingAugmentedStages

/-!
概要：任意の指定余錐を固定した標的の slice 内の全図式として表示する。
方針：元の全余錐を curry し、射影と全展開を回収する。
規約：指定された余錐と頂点を選び直さない。
使われ方：交互図式の偶数部分列を元の表示余錐の上で比較する。

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

/-- 概要：元の指定余錐から固定標的の slice 内の全図式を構成する。
方針：右制限を元の余錐頂点の Yoneda 表示に揃えて curry する。
規約：元の全余錐値を保持する。
使われ方：表示図式を元の対象上で比較する。 -/
def coconeSliceDiagram {K C : SSet.{u}} {F : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry c.val (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, Equiv.symm_apply_apply])

/-- 概要：元の余錐の slice 表示の全展開は元の余錐そのもの。
方針：curry と uncurry の逆関係。
規約：全射の等式。
使われ方：全増大余錐の比較。 -/
lemma coconeSliceDiagram_uncurry {K C : SSet.{u}} {F : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (coconeSliceDiagram c) = c.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry _ _

/-- 概要：元の余錐の slice 表示は元の全底図式を射影する。
方針：curry の射影式と余錐の固定条件。
規約：全射の等式。
使われ方：元の compact 表示図式の回収。 -/
lemma coconeSliceDiagram_projection {K C : SSet.{u}} {F : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    coconeSliceDiagram c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c.vertex) = F := by
  rw [coconeSliceDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection]
  exact c.property

/-- 概要：全交互段の偶数制限は元の表示余錐の slice 図式の制限そのもの。
方針：全 uncurry の単射性と全偶数増大余錐の等式を使う。
規約：固定標的 slice 内の全射の厳密な等式。
使われ方：全可算偶数部分列の比較。 -/
lemma AlternatingPresentationStage.even_sliceDiagram
    {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n) ≫ s.sliceDiagram =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index ≫ coconeSliceDiagram c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (SSet.yonedaEquiv.symm c.vertex)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, s.sliceDiagram_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, coconeSliceDiagram_uncurry]
  exact s.augmentation_eq

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
