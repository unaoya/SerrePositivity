module

public import SerrePositivity.KST.Spectra.WeightedConeTriangleEdgewise

/-!
概要：反転係数を元の区間の経路へ戻すと、元の係数の終点から始点への順になる。
方針：Yoneda の区間の両端と、反転による二つの面の交換を厳密計算する。
規約：元の係数の頂点番号を明示。使われ方：元の円評価錐との比較の向きの検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 元の一単体の区間写像の i 頂点は、反対側の面番号の零単体。 -/
lemma simplexInterval_vertex {X : SSet.{u}} (a : X _⦋1⦌) (i : Fin 2) :
    (SSet.yonedaEquiv.symm a).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) =
      X.δ i.rev a := by
  have hi : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.{u}.symm i) =
      SimplexCategory.δ i.rev := by fin_cases i <;> decide
  rw [SSet.yonedaEquiv_symm_app, hi]
  rfl

/-- 区間写像の Yoneda 一単体の面は、元の区間写像の同じ端点の値。 -/
lemma intervalMap_yoneda_face {X : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ X) (i : Fin 2) :
    X.δ i.rev (SSet.yonedaEquiv f) =
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) := by
  have h := (simplexInterval_vertex (SSet.yonedaEquiv f) i).symm
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- 反転係数を戻した経路の始点は、元の反転係数の終点の基礎零単体。 -/
lemma reflectedCoefficient_source {X : SSet.{u}} (τ : (Δ[1] : SSet.{u}) ⟶ X.op) :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap τ).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      SSet.opObjEquiv (τ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) := by
  rw [reflectedCoefficient_unreverse, simplexInterval_vertex, SSet.δ_opObjEquiv]
  exact congrArg SSet.opObjEquiv (intervalMap_yoneda_face τ 1)

/-- 反転係数を戻した経路の終点は、元の反転係数の始点の基礎零単体。 -/
lemma reflectedCoefficient_target {X : SSet.{u}} (τ : (Δ[1] : SSet.{u}) ⟶ X.op) :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap τ).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
      SSet.opObjEquiv (τ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) := by
  rw [reflectedCoefficient_unreverse, simplexInterval_vertex, SSet.δ_opObjEquiv]
  exact congrArg SSet.opObjEquiv (intervalMap_yoneda_face τ 0)

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
