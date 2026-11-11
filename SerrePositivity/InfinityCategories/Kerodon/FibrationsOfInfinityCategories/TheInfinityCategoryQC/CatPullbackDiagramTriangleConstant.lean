module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.StrictDiagramTriangleConstant
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackDiagramComparisonIsos

/-!
概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramUpperTriangle_constant (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsConstantCoherentTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramUpperTriangle p q f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isConstantCoherentTriangle_natTrans_upper (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy_diagram p q
/-- 概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramLowerTriangle_constant (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsConstantCoherentTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramLowerTriangle p q f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isConstantCoherentTriangle_natTrans_lower (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy_diagram p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
