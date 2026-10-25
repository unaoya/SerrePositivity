module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseBoundaryColumns
/-!
概要：任意の pinched 線形単体の逆係数は、全標準面の境界式と零次の閉性を満たす。
方針：全部分集合の線形削除式を全頂点集合へ適用し、面の次数輸送を比較する。
規約：実 Hom の微分と全パラメーター次数を維持する。
使われ方：逆構成の HA パラメーター側の和と Leibniz 項の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarInverseParameterCoefficient_degree_heq
    {R : Type u} [CommRing R] {C : Type v} [DGCategory R C] {x y : C} {n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R x y n) (J : Finset (Fin (n + 1)))
    (k l : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hl : l = 1 - (J.card : ℤ)) (hkl : k = l) :
    HEq (dgCoherentBarInverseParameterCoefficient f J k hJ hk)
      (dgCoherentBarInverseParameterCoefficient f J l hJ hl) := by
  cases hkl
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseFullHom_closed_zero
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N 0) :
    differential R (dgCoherentBarInverseFullHom R D F hMC N f.val) = 0 :=
  dgCoherentBarInverseParameterCoefficient_closed_singleton f Finset.univ 0
    Finset.univ_nonempty (by simp) (by simp)

lemma dgCoherentBarInverseFullHom_differential {m : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N
      (m + 1)) :
    differential R (dgCoherentBarInverseFullHom R D F hMC N f.val) =
      dgCoherentBarInverseBoundary R D F hMC N f.val := by
  have hd := dgCoherentBarInverseParameterCoefficient_differential f Finset.univ
    (-((m + 1 : ℕ) : ℤ)) Finset.univ_nonempty (by simp) (by simp)
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ] at hd
  rw [hd]
  unfold dgCoherentBarInverseBoundary
  apply Finset.sum_congr rfl
  intro a _
  rw [dgCoherentBarFin_strictRight_card]
  have hle : a.val ≤ m + 1 := by have := a.isLt; omega
  rw [Nat.cast_sub hle]
  congr 1
  have hC := dgCoherentBarInverseParameterCoefficient_degree_heq f.val
    (Finset.univ.erase a) (-((m + 1 : ℕ) : ℤ) + 1) (-(m : ℤ))
    (Finset.card_pos.mp (by simp)) (by simp) (by simp) (by omega)
  have hT := gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (dgCoherentBarInverseFaceHom R D F hMC N f.val a)
  exact eq_of_heq (hC.trans hT.symm)

end SerrePositivity.InfinityCategories
