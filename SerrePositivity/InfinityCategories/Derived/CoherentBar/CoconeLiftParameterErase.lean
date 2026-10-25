module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterData
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceSum
/-!
概要：動く右面について、パラメーターの内部頂点を消した混合 HA 成分を、型付きの回収削除 Hom へ同定する。
方針：全先頭集合と一点削除したパラメーター集合の因数分解を使う。
規約：正次数の任意の余錐族と零次元を含む任意の元の単体を扱う。
使われ方：混合 HA のパラメーター側の削除和を標準面の和へ移す。
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

lemma dgCoherentBarCoconeLiftFullErase_parameter {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullErase
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgCoherentBarCoconeLiftTarget R D F c)
        (dgCoherentBarCoconeLiftParameterErase R D F hMC c j)
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let L : Finset (Fin (m + 2)) := Finset.univ.erase j.castSucc
  have hcL : L.card = m + 1 := by simp [L]
  have hj : dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hSet : dgCoherentBarJoinSubset (Finset.univ : Finset (Fin (n + 1))) L =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).erase (j.natAdd n).succ.castSucc := by
    change dgCoherentBarJoinSubset Finset.univ (Finset.univ.erase j.castSucc) = _
    rw [← dgCoherentBarJoinSubset_erase_right, dgCoherentBarJoinSubset_univ, hj]
  let K : Finset (Fin (n + 1)) := Finset.univ
  have hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card := by
    rw [dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (0 : Fin (n + (m + 1) + 2)) =
      (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ) := by
    have h0 : (0 : Fin (n + (m + 1) + 2)) ∈ dgCoherentBarJoinSubset K L := by
      rw [hSet]
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos (j.natAdd n))),
          Finset.mem_univ _⟩
    exact le_antisymm (Fin.zero_le _) (Finset.min'_le _ 0 h0)
  have hb : Fin.last (n + (m + 1) + 1) =
      (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ) := by
    have hl : Fin.last (n + (m + 1) + 1) ∈ dgCoherentBarJoinSubset K L := by
      rw [hSet]
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩
    exact le_antisymm (Finset.le_max' _ _ hl) (Fin.le_last _)
  have hk : -((n + (m + 1) : ℕ) : ℤ) + 1 =
      2 - ((dgCoherentBarJoinSubset K L).card : ℤ) := by
    rw [dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    omega
  have hF := dgCoherentBarCoconeLiftSimplex_subset_factorization R D F hMC
    (r := n) (l := m) c s K L (by simp [K]) hcL
    (dgCoherentBarParameterErase_nonempty j)
    0 (Fin.last (n + (m + 1) + 1)) (-((n + (m + 1) : ℕ) : ℤ) + 1) hJ ha hb hk
  simp only [K, L] at hF
  have hLabel := dgCoherentBarSubsetLabel_univ s
  have hSource := congrArg (dgCoherentBarSource R D F) hLabel
  have hColumn := dgCoherentBarNativeColumn_heq_of_index_eq R D F hMC hLabel
  have hErase : HEq (dgCoherentBarCoconeLiftParameterErase R D F hMC c j)
      (dgCoherentBarCoconeLiftSubsetHom R D F hMC c (Finset.univ.erase j.castSucc)
        (-(m : ℤ)) (dgCoherentBarParameterErase_nonempty j) (by simp)) := by
    unfold dgCoherentBarCoconeLiftParameterErase
    exact gradedHomTransport_heq _ _ _ _
  have hObj := congrArg (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
    (dgCoherentBarParameterErase_max j)
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hSource rfl hObj rfl rfl
    (show -(m : ℤ) - (n : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)
    (p := -(n : ℤ)) (q := -(m : ℤ)) (k := -(m : ℤ) - (n : ℤ))
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarCoconeLiftSubsetHom R D F hMC c (Finset.univ.erase j.castSucc)
      (-(m : ℤ)) (dgCoherentBarParameterErase_nonempty j) (by simp))
    (dgCoherentBarNativeColumn R D F hMC
      (dgCoherentBarSubsetLabel s Finset.univ n (by simp)))
    (dgCoherentBarCoconeLiftParameterErase R D F hMC c j)
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    hErase.symm hColumn (by omega) (by omega)
  refine HEq.trans ?_ (hF.trans hComp)
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories
