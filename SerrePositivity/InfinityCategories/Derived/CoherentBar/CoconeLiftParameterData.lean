module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubsetFactorization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterRightCut
/-!
概要：動く右面のパラメーター削除・前部・後部の三成分を型付きで保持する。
方針：削除と前部には回収 Hom、後部には元の右面の実 HA 成分を使う。
規約：定値性による消去はせず、動く切断点の対象を保つ。
使われ方：標準 Hom の持ち上げのパラメーター HA 境界式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

def dgCoherentBarParameterPrefix {m : ℕ} (j : Fin (m + 1)) : Finset (Fin (m + 2)) :=
  Finset.univ.filter (· ≤ j.castSucc)

lemma dgCoherentBarParameterPrefix_card {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).card = j.val + 1 :=
  dgCoherentBarPrefix_card (m + 1) j.castSucc

lemma dgCoherentBarParameterPrefix_nonempty {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).Nonempty :=
  ⟨j.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩

lemma dgCoherentBarParameterPrefix_max {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).max' (dgCoherentBarParameterPrefix_nonempty j) =
      j.castSucc := by
  apply le_antisymm
  · exact Finset.max'_le (dgCoherentBarParameterPrefix j)
      (dgCoherentBarParameterPrefix_nonempty j) j.castSucc
      (fun x hx => (Finset.mem_filter.mp hx).2)
  · exact Finset.le_max' (dgCoherentBarParameterPrefix j) j.castSucc
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)

lemma dgCoherentBarParameterErase_nonempty {m : ℕ} (j : Fin (m + 1)) :
    ((Finset.univ : Finset (Fin (m + 2))).erase j.castSucc).Nonempty :=
  ⟨Fin.last (m + 1), Finset.mem_erase.mpr
    ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩⟩

lemma dgCoherentBarParameterErase_max {m : ℕ} (j : Fin (m + 1)) :
    ((Finset.univ : Finset (Fin (m + 2))).erase j.castSucc).max'
      (dgCoherentBarParameterErase_nonempty j) = Fin.last (m + 1) := by
  apply le_antisymm
  · exact Fin.le_last _
  · exact Finset.le_max' _ _ (Finset.mem_erase.mpr
      ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarCoconeLiftParameterErase {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ)) :=
  gradedHomTransport rfl
    (congrArg (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
      (dgCoherentBarParameterErase_max j)) rfl
    (dgCoherentBarCoconeLiftSubsetHom R D F hMC c (Finset.univ.erase j.castSucc)
      (-(m : ℤ)) (dgCoherentBarParameterErase_nonempty j) (by simp))

def dgCoherentBarCoconeLiftParameterPrefix {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc) (-(j.val : ℤ)) :=
  gradedHomTransport rfl
    (congrArg (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
      (dgCoherentBarParameterPrefix_max j)) rfl
    (dgCoherentBarCoconeLiftSubsetHom R D F hMC c (dgCoherentBarParameterPrefix j)
      (-(j.val : ℤ)) (dgCoherentBarParameterPrefix_nonempty j)
      (by rw [dgCoherentBarParameterPrefix_card]; push_cast; omega))

def dgCoherentBarCoconeLiftParameterTail {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc)
      (dgCoherentBarCoconeLiftTarget R D F c) ((j.val : ℤ) - (m : ℤ)) :=
  gradedHomTransport rfl rfl (show 2 - ((dgCoherentBarParameterTail j).card : ℤ) =
      (j.val : ℤ) - (m : ℤ) by
    rw [dgCoherentBarParameterTail_card]
    have := j.isLt
    omega)
    (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).hom
      (dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
      (2 - ((dgCoherentBarParameterTail j).card : ℤ)) (dgCoherentBarParameterTail_two j)
      (dgCoherentBarParameterTail_min j) (dgCoherentBarParameterTail_max j) rfl)

def dgCoherentBarCoconeLiftParameterTerm {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ)) :=
  (((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
    (dgCoherentBarCoconeLiftParameterErase R D F hMC c j -
      compose R (dgCoherentBarCoconeLiftParameterTail R D F c j)
        (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
        (show -(j.val : ℤ) + ((j.val : ℤ) - (m : ℤ)) = -(m : ℤ) by omega))

end SerrePositivity.InfinityCategories
