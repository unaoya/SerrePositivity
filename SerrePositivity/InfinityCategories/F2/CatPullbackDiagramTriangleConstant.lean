module

public import SerrePositivity.InfinityCategories.F2.StrictDiagramTriangleConstant
public import SerrePositivity.InfinityCategories.F2.CatPullbackDiagramComparisonIsos

/-!
概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramUpperTriangle_constant (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsConstantCoherentTriangle (catPullbackDiagramUpperTriangle p q f) := by
  apply isConstantCoherentTriangle_natTrans_upper (catPullbackReplacementNatTrans p q)
  exact catPullbackConeHomotopy_diagram p q
/-- 概要：引き戻し図式の指定上下三角形の定値性。
方針：全錐の制限が切断の strict な円柱と一致することを使う。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramLowerTriangle_constant (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsConstantCoherentTriangle (catPullbackDiagramLowerTriangle p q f) := by
  apply isConstantCoherentTriangle_natTrans_lower (catPullbackReplacementNatTrans p q)
  exact catPullbackConeHomotopy_diagram p q

end SerrePositivity.InfinityCategories.F2
