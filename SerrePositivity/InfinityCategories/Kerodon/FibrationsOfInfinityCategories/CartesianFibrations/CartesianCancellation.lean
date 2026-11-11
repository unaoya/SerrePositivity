module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：三角形の cartesian 辺の消去則。
方針：三角形を反転して cocartesian 辺の消去則を適用する。
規約：底は quasicategory、射は inner fibration。
使われ方：同じ終点を持つ cartesian な持ち上げの比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：後半の辺と長辺が cartesian なら三角形の最初の辺も cartesian。
方針：反転後の最初の辺と長辺を cocartesian な消去則に渡す。
規約：辺の等式は反転した単体の面の計算で保持する。
使われ方：cartesian な二つの輸送の間の垂直辺の可逆性。 -/
@[kerodon 01TS]
lemma isCartesianEdge_triangle_first_of_second_long {X B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (p : X ⟶ B) [InnerFibration p]
    (hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (hlong : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)) := by
  let top : (Δ[2] : SSet.{u}) ⟶ X.op :=
    SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.yonedaEquiv t))
  have hf (i : Fin 3) : SSet.yonedaEquiv (stdSimplex.δ i ≫ top) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ i.rev ≫ t)) := by
    dsimp only [top]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.op_δ,
      Equiv.apply_symm_apply, ← stdSimplex.yonedaEquiv_δ_comp]
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ top)) := by
    rw [hf]
    exact hsecond.op
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ top)) := by
    rw [hf]
    exact hlong.op
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_second_of_first_long top
    (SSet.opFunctor.map p) h₀ h₁
  rw [hf] at h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isCocartesianEdge_op p _ h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
