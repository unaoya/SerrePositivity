module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterErase
/-!
概要：動く右面の全パラメーター切断の左因子を、回収前部 Hom と native 列へ分解する。
方針：任意の右前部集合の混合因数分解を使う。
規約：実際の HA 成分を用い、端点と次数を異種等号で保持する。
使われ方：全切断合成を回収データの非線形 HA 項へ移す。
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

lemma dgCoherentBarCoconeLiftFullLeft_parameter {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullLeft
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := ((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc)
        (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ
  let L := dgCoherentBarParameterPrefix j
  let v := (j.natAdd n).succ.castSucc
  have hcL : L.card = j.val + 1 := dgCoherentBarParameterPrefix_card j
  have hj : dgCoherentBarJoinRight n (m + 1) j.castSucc = v :=
    Fin.ext (by change n + 1 + j.val = n + j.val + 1; omega)
  have hSet : dgCoherentBarJoinSubset K L =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter (· ≤ v) := by
    have h := dgCoherentBarJoinSubset_filter_le_right K
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    simp only [K] at h
    rw [dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card := by
    rw [dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (0 : Fin (n + (m + 1) + 2)) =
      (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have hb : v = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
    · apply Finset.max'_le
      intro x hx
      rw [hSet] at hx
      exact (Finset.mem_filter.mp hx).2
  let k : ℤ := 2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
    (· ≤ v)).card : ℤ)
  have hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ) := by rw [hSet]
  have hF := dgCoherentBarCoconeLiftSimplex_subset_factorization R D F hMC
    (r := n) (l := j.val) c s K L (by simp [K]) hcL
    (dgCoherentBarParameterPrefix_nonempty j) 0 v k hJ ha hb hk
  simp only [K] at hF
  have hLabel := dgCoherentBarSubsetLabel_univ s
  have hSource := congrArg (dgCoherentBarSource R D F) hLabel
  have hColumn := dgCoherentBarNativeColumn_heq_of_index_eq R D F hMC hLabel
  have hPrefix : HEq (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
      (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
        (dgCoherentBarParameterPrefix_nonempty j)
        (by rw [hcL]; push_cast; omega)) := by
    unfold dgCoherentBarCoconeLiftParameterPrefix
    exact gradedHomTransport_heq _ _ _ _
  have hObj := congrArg (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
    (dgCoherentBarParameterPrefix_max j)
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hSource rfl hObj rfl rfl
    (show -(j.val : ℤ) - (n : ℤ) = -(n : ℤ) + -(j.val : ℤ) by omega)
    (p := -(n : ℤ)) (q := -(j.val : ℤ)) (k := -(j.val : ℤ) - (n : ℤ))
    (p' := -(n : ℤ)) (q' := -(j.val : ℤ)) (k' := -(n : ℤ) + -(j.val : ℤ))
    (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
      (dgCoherentBarParameterPrefix_nonempty j) (by rw [hcL]; push_cast; omega))
    (dgCoherentBarNativeColumn R D F hMC
      (dgCoherentBarSubsetLabel s Finset.univ n (by simp)))
    (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    hPrefix.symm hColumn (by omega) rfl
  refine HEq.trans ?_ (hF.trans hComp)
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories
