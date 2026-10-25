module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearData
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterFaces
/-!
概要：回収した pinched 成分族の全頂点と一点削除の成分を計算する。
方針：全頂点の列挙は恒等、一点削除の列挙は標準面であることを再利用する。
規約：右 pinched 規約への次数符号と整数次数の輸送を保持する。
使われ方：全頂点の線形方程式を既に証明した Hom の境界式へ帰着する。
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

lemma dgCoherentBarCoconeLinearData_full_component {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    (dgCoherentBarCoconeLinearData R D F hMC y c).component Finset.univ (-(n : ℤ))
      Finset.univ_nonempty (by simp) =
      (n : ℤ).negOnePow • dgCoherentBarCoconeFamilyHom R D F hMC y c := by
  have h := dgCoherentBarCoconeSubsetHom_heq R D F hMC y c Finset.univ (-(n : ℤ))
    Finset.univ_nonempty (by simp) n (by simp)
  unfold dgCoherentBarCoconeSubsetParameterHom at h
  rw [dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at h
  exact eq_of_heq h

lemma dgCoherentBarCoconeLinearData_erase_component_heq {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (a : Fin (m + 2)) (k : ℤ)
    (hJ : ((Finset.univ : Finset (Fin (m + 2))).erase a).Nonempty)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (m + 2))).erase a).card : ℤ)) :
    HEq ((dgCoherentBarCoconeLinearData R D F hMC y c).component
      (Finset.univ.erase a) k hJ hk)
      ((m : ℤ).negOnePow • dgCoherentBarCoconeFamilyHom R D F hMC y
        ((coconeMappingSpace F y).δ a c)) := by
  have h := dgCoherentBarCoconeSubsetHom_heq R D F hMC y c (Finset.univ.erase a)
    k hJ hk m (by simp)
  unfold dgCoherentBarCoconeSubsetParameterHom at h
  rw [dgCoherentBarErase_orderHom] at h
  exact h

lemma dgCoherentBarCoconeLinearData_erase_boundary_component {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (a : Fin (m + 2))
    (hJ : ((Finset.univ : Finset (Fin (m + 2))).erase a).Nonempty)
    (hk : -((m + 1 : ℕ) : ℤ) + 1 =
      1 - (((Finset.univ : Finset (Fin (m + 2))).erase a).card : ℤ)) :
    (dgCoherentBarCoconeLinearData R D F hMC y c).component
      (Finset.univ.erase a) (-((m + 1 : ℕ) : ℤ) + 1) hJ hk =
      (m : ℤ).negOnePow • dgCoherentBarCoconeFaceHom R D F hMC y c a := by
  have h := dgCoherentBarCoconeLinearData_erase_component_heq R D F hMC y c a
    (-((m + 1 : ℕ) : ℤ) + 1) hJ hk
  have hF : HEq (dgCoherentBarCoconeFaceHom R D F hMC y c a)
      (dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).δ a c)) :=
    gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
      (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega) _
  have hS := dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    rfl rfl (show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega)
    (m : ℤ).negOnePow _ _ hF
  exact eq_of_heq (h.trans hS.symm)

end SerrePositivity.InfinityCategories
