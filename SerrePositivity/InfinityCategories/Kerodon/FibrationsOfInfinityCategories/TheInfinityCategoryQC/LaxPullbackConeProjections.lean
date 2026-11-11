module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg

/-!
概要：native な lax pullback の錐の脚の回収。
方針：strict な錐の脚の一単体を既存の射影と同定する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：native な lax pullback の脚は指定射影の coherent 辺。
方針：通常の引き戻し錐の二つの脚を回収する。
規約：辺の類だけでなく元の一単体を保持する。
使われ方：全試験関手 core の表示と native な極限錐の接続。 -/
lemma laxPullbackCone_arrow (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCone p q)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackObject p q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatArrowObject C from
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackOrdinaryCone p q) _
/-- 概要：native な lax pullback の脚は指定射影の coherent 辺。
方針：通常の引き戻し錐の二つの脚を回収する。
規約：辺の類だけでなく元の一単体を保持する。
使われ方：全試験関手 core の表示と native な極限錐の接続。 -/
lemma laxPullbackCone_inputs (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCone p q)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackObject p q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatTensorObject A B from
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackOrdinaryCone p q) _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
