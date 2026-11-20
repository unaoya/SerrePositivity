module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.FiberTriangleReduction
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：相対三角形の三辺の積と実際の連結準同型の一致。
方針：先頭辺を相対充填で消去し、最後の二面を既存の終端ホーンでまとめる。
規約：基本群の非可換な積の順序を保持する。
使われ方：Goerss–Jardine I §8、VIII §1。cochain 次数一の境界公式。
-/

@[expose] public section
universe u v
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FiberTriangle
end SerrePositivity.KST.Spectra.FiberTriangle
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.FiberTriangle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 底の二単体の連結像は、三辺の指定した順序の積。 -/
theorem connecting_product {E B : SSet.{u}} {p : E ⟶ B}
    [Fibration p] [KanComplex E] [KanComplex B] {e : E _⦋0⦌}
    {s : B.PtSimplex 2 (p.app _ e)}
    {a : Fin 3 → (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)}
    (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 1))⁻¹ * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 2) *
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 0) := by
  obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse (a 0) (0 : Fin 1)
  obtain ⟨b, ⟨hb⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_left_factor ia (a 2) (0 : Fin 1)
  let T' := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce hi hb T
  obtain ⟨ia₁, ⟨hi₁⟩⟩ := PtSimplex.MulStruct.exists_left_inverse
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced a b (1 : Fin 3)) (0 : Fin 1)
  obtain ⟨c, ⟨hc⟩⟩ := PtSimplex.MulStruct.nonempty ia₁
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced a b (2 : Fin 3)) (0 : Fin 1)
  have hlower : ∀ j : Fin 3, j.val < 1 → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced a b j = .const := by
    intro j hj
    have hj' : j = 0 := Fin.ext (by omega)
    subst j
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced]
  have hconn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk c := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.terminalLift hi₁ hc T' hlower),
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.terminalLift_boundary]
    rfl
  have hi' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ia = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 0))⁻¹ :=
    eq_inv_of_mul_eq_one_left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hi)
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 2) *
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 0) := by
    have h := eq_mul_inv_of_mul_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hb)
    simpa only [hi', inv_inv] using h
  have hi₁' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ia₁ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a 1))⁻¹ := by
    have h := eq_inv_of_mul_eq_one_left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hi₁)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced, Fin.reduceEq, ite_false] using h
  rw [hconn, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hc]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced, Fin.reduceEq, ite_false, ite_true]
  rw [hi₁', hb', mul_assoc]

/-- 可換群へ移した三辺の交代和は、底の二単体の連結像。 -/
theorem alternating_connecting {E B : SSet.{u}} {p : E ⟶ B}
    [Fibration p] [KanComplex E] [KanComplex B] {e : E _⦋0⦌}
    {s : B.PtSimplex 2 (p.app _ e)}
    {a : Fin 3 → (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)}
    (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a) {G : Type v} [CommGroup G]
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) →* G) :
    (∑ j : Fin 3, (-1 : ℤ) ^ j.val • Additive.ofMul (φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a j)))) =
      Additive.ofMul (φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.connecting_product T, φ.map_mul, φ.map_mul, φ.map_inv]
  simp only [ofMul_mul, ofMul_inv, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
    one_zsmul, Fin.val_succ, Fin.sum_univ_zero, add_zero]
  norm_num
  abel

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
