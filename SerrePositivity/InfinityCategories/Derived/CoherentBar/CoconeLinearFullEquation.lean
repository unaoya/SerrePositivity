module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearFullCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearEquationTransfer
public import SerrePositivity.InfinityCategories.DGNerve.Residual
/-!
概要：回収した pinched 成分族は全頂点集合で線形単体方程式を満たす。
方針：全成分と一点削除の成分を Hom の境界式へ直し、次数符号を比較する。
規約：零次元の閉性と正次数の境界式を同じ元の実 Hom で扱う。
使われ方：既存の単射方程式移送により全部分集合の線形方程式を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeLinearData_full_equation {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    differential R ((dgCoherentBarCoconeLinearData R D F hMC y c).component
      Finset.univ (-(n : ℤ)) Finset.univ_nonempty (by simp)) =
      (dgCoherentBarCoconeLinearData R D F hMC y c).rhs Finset.univ (-(n : ℤ)) (by simp) := by
  cases n with
  | zero =>
    rw [dgCoherentBarCoconeLinearData_full_component]
    simp only [Nat.cast_zero, Int.negOnePow_zero, one_smul]
    change (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)).d 0 1
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) = _
    rw [dgCoherentBarCoconeFamilyHom_closed_zero]
    simp [DGNerve.PinchedHom.LinearData.rhs]
  | succ m =>
    rw [dgCoherentBarCoconeLinearData_full_component, differential_units_smul,
      dgCoherentBarCoconeFamilyHom_differential]
    unfold dgCoherentBarCoconeFamilyHomBoundary
    rw [Finset.smul_sum]
    unfold DGNerve.PinchedHom.LinearData.rhs
    rw [dite_eq_left (show 2 ≤ (Finset.univ : Finset (Fin (m + 2))).card by simp)]
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
    apply Finset.sum_congr rfl
    intro a _
    rw [dgCoherentBarCoconeLinearData_erase_boundary_component,
      dgCoherentBarFin_strictRight_card]
    rw [smul_smul, smul_smul]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    rw [Nat.cast_sub (show a.val ≤ m + 1 by have := a.isLt; omega)]
    push_cast
    omega

end SerrePositivity.InfinityCategories
