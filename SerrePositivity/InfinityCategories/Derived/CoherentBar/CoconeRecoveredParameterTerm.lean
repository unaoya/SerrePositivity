module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterLeft
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterRight
/-!
概要：回収した一点下のデータの全 HA 項は、回収 Hom の微分式の各項に一致する。
方針：実端点と次数を保って削除・左右切断の三つの比較を合成する。
規約：回収データの HA 方程式を先取りしない。
使われ方：実微分式から一点下の HA 方程式を証明する。
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

lemma dgCoherentBarCoconeRecoveredFullTerm_parameter {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullTerm (dgCoherentBarCoconeRecoveredRawData R D F hMC c)
      (j.natAdd 0)) (dgCoherentBarCoconeLiftParameterTerm R D F hMC c j) := by
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c
  let U := (sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c
  let p : ℤ := 2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
    (· ≤ (j.natAdd 0).succ.castSucc)).card : ℤ)
  let q : ℤ := 2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
    ((j.natAdd 0).succ.castSucc ≤ ·)).card : ℤ)
  have hp : p = -(j.val : ℤ) := by
    dsimp only [p]
    rw [dgCoherentBarFullLeft_card]
    simp only [Fin.val_natAdd]
    omega
  have hq : q = (j.val : ℤ) - (m : ℤ) := by
    dsimp only [q]
    rw [dgCoherentBarFullRight_card]
    simp only [Fin.val_natAdd]
    have := j.isLt
    omega
  have hOut : -((0 + (m + 1) : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
  have hx := dgCoherentBarCoconeRecoveredRawData_source R D F hMC c
  have hz := dgCoherentBarCoconeRecoveredRawData_target R D F hMC c
  have hj : dgCoherentBarJoinRight 0 (m + 1) j.castSucc =
      (j.natAdd 0).succ.castSucc := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hy : Q.obj (j.natAdd 0).succ.castSucc = U.obj j.castSucc := by
    have h := congrArg (fun a : SimplexData R (RightModule R D) (m + 1) => a.obj j.castSucc)
      (dgCoherentBarCoconeRecoveredRawData_right R D F hMC c)
    change Q.obj (dgCoherentBarJoinRight 0 (m + 1) j.castSucc) = _ at h
    rwa [hj] at h
  have hCut := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hz hp hq hOut
    (p := p) (q := q) (k := -((0 + (m + 1) : ℕ) : ℤ) + 1)
    (p' := -(j.val : ℤ)) (q' := (j.val : ℤ) - (m : ℤ)) (k' := -(m : ℤ))
    (dgCoherentBarFullRight Q (j.natAdd 0)) (dgCoherentBarFullLeft Q (j.natAdd 0))
    (dgCoherentBarCoconeLiftParameterTail R D F c j)
    (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
    (dgCoherentBarCoconeRecoveredFullRight_parameter_tail R D F hMC c j)
    (dgCoherentBarCoconeRecoveredFullLeft_parameter R D F hMC c j)
    (by rw [hp, hq]; omega) (by omega)
  unfold dgCoherentBarCoconeLiftParameterTerm
  rw [dgCoherentBarFullTerm_eq_composite, dgCoherentBarFullTerm_sign_right,
    dgCoherentBarFullTerm_sign]
  apply dgCoherentBarHom_units_smul_heq hx hz hOut
  apply gradedHom_sub_heq hx hz hOut
  · exact dgCoherentBarCoconeRecoveredFullErase_parameter R D F hMC c j
  · exact hCut

end SerrePositivity.InfinityCategories
