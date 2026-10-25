module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterData
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredRightHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents
/-!
概要：回収した一点下のデータについて、パラメーターで切った HA 右因子を、動く右面の実成分へ直す。
方針：右区間の尾部集合の像と、純粋右面の成分比較を使う。
規約：定値性を仮定せず、実 dg HA 成分を保持する。
使われ方：全切断合成を型付きの回収 HA 項へ移す。
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

lemma dgCoherentBarCoconeRecoveredFullRight_parameter {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
      (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).hom
        (dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((dgCoherentBarParameterTail j).card : ℤ)) (dgCoherentBarParameterTail_two j)
        (dgCoherentBarParameterTail_min j) (dgCoherentBarParameterTail_max j) rfl) := by
  let T := (dgCoherentBarCoconeRecoveredRawData R D F hMC c)
  let L := dgCoherentBarParameterTail j
  have hj : dgCoherentBarJoinRight 0 (m + 1) j.castSucc =
      (j.natAdd 0).succ.castSucc := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hl : dgCoherentBarJoinRight 0 (m + 1) (Fin.last (m + 1)) =
      Fin.last (0 + (m + 1) + 1) := Fin.ext (by
    change 0 + 1 + (m + 1) = 0 + (m + 1) + 1
    omega)
  have hSet : L.image (dgCoherentBarJoinRight 0 (m + 1)) =
      (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
        ((j.natAdd 0).succ.castSucc ≤ ·) := by
    have h := dgCoherentBarJoinSubset_filter_right_le
      (Finset.univ : Finset (Fin (0 + 1)))
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hd : (2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
      ((j.natAdd 0).succ.castSucc ≤ ·)).card : ℤ)) = 2 - (L.card : ℤ) := by
    rw [← hSet, Finset.card_image_of_injective _
      (dgCoherentBarJoinRight_injective 0 (m + 1))]
  have hPure := dgCoherentBarCoconeRecoveredRawData_pure_right_hom_heq R D F hMC c L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (dgCoherentBarParameterTail_two j) (dgCoherentBarParameterTail_min j)
    (dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarCoconeRecoveredFullRight_parameter_tail {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
      (dgCoherentBarCoconeLiftParameterTail R D F c j) := by
  refine (dgCoherentBarCoconeRecoveredFullRight_parameter R D F hMC c j).trans ?_
  unfold dgCoherentBarCoconeLiftParameterTail
  exact (gradedHomTransport_heq _ _ _ _).symm

end SerrePositivity.InfinityCategories
