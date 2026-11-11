module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteFamilyUpdate
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SSetProductEvaluation

/-!
概要：離散図式の一成分更新の頂点と元の成分の値を照合する。
方針：全評価関手の等式を零単体へ適用し、離散図式の頂点外延性を使う。
規約：元の全図式の頂点を保持する。
使われ方：有限添字の帰納法と Yoneda 生成対象での比較の検出。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} {X : SSet.{u + 1}}
local instance : DecidableEq I := Classical.decEq I

/-- 概要：元の一成分更新全関手の指定頂点の図式。
方針：関手頂点の表示同値の逆を使う。
規約：全関手の実際の零単体を使う。
使われ方：各座標の元の全図式。 -/
def discreteFamilyUpdatedDiagram
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (i : I) (x : X _⦋0⦌) : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i).app (Opposite.op ⦋0⦌) x)

/-- 概要：更新後の図式は元の更新全関手の指定零単体そのもの。
方針：関手頂点の表示同値の往復を使う。
規約：元の頂点を保持する。
使われ方：比較を更新全関手で制限した成分の照合。 -/
lemma discreteFamilyUpdatedDiagram_vertex
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (i : I) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discreteFamilyUpdatedDiagram p i x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i).app (Opposite.op ⦋0⦌) x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _

/-- 概要：更新後の各成分は指定座標の変数値か元の成分値。
方針：全評価関手の公式を同じ零単体で読む。
規約：元の小さい離散添字を使う。
使われ方：有限座標の帰納法の仮定の確認。 -/
lemma discreteFamilyUpdatedDiagram_evaluate
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (i j : I) (x : X _⦋0⦌) :
    (discreteFamilyUpdatedDiagram p i x).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) =
      if j = i then x else p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))
    (discreteFamilyUpdatedDiagram p i x)
  rw [discreteFamilyUpdatedDiagram_vertex] at he
  have h := congrArg (fun f : X ⟶ X ↦ f.app (Opposite.op ⦋0⦌) x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate_evaluate p i j)
  rw [← he]
  by_cases hj : j = i
  · rw [ite_eq_left hj] at h ⊢
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i).app (Opposite.op ⦋0⦌) x) = x at h
    exact h
  · rw [ite_eq_right hj] at h ⊢
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i).app (Opposite.op ⦋0⦌) x) =
      (SSet.const (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) : X ⟶ X).app
        (Opposite.op ⦋0⦌) x at h
    exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply _ x)

/-- 概要：指定座標を元の成分に戻すと元の全離散図式を回収する。
方針：元の全成分の等式から離散図式の外延性を使う。
規約：全図式の射を厳密に回収する。
使われ方：全比較の任意の成分を各座標で検出する。 -/
lemma discreteFamilyUpdatedDiagram_original
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) (i : I) :
    discreteFamilyUpdatedDiagram p i
      (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))) = p := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftedDiscreteDiagram_hom_ext
  intro j
  rw [discreteFamilyUpdatedDiagram_evaluate]
  by_cases h : j = i
  · subst j
    exact ite_eq_left rfl
  · exact ite_eq_right h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
