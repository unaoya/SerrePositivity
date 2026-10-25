module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceErase
/-!
概要：持ち上げ余錐について、元の内部頂点で切った混合 HA の右因子を、高次 Hom と native の右因子へ分解する。
方針：末尾の先頭集合と全パラメーターの混合因数分解を適用する。
規約：全整数次数の実加群 Hom と同じ Koszul 合成を使う。
使われ方：混合 HA 切断合成を、native HA 項の後合成へ直す。
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

lemma dgCoherentBarCoconeLiftFullRight_source {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) (i : Fin n) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (i.castAdd m))
      (compose R (dgCoherentBarCoconeLiftHomAt R D F hMC c s)
        (dgCoherentBarFullRight (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
        rfl) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let S := (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ.filter (i.succ ≤ ·)
  let L : Finset (Fin (m + 1)) := Finset.univ
  let r := n - (i.val + 1)
  have hc : K.card = r + 1 := dgCoherentBarTail_card n i.succ
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  have hm : i.succ = K.min' hK := Index.right_min (Finset.mem_univ _) hK
  have hSetT : dgCoherentBarJoinSubset K L =
      (Finset.univ : Finset (Fin (n + m + 2))).filter
        ((i.castAdd m).succ.castSucc ≤ ·) := by
    have h := dgCoherentBarJoinSubset_filter_left_le
      (Finset.univ : Finset (Fin (n + 1))) L i.succ
    change _ = dgCoherentBarJoinSubset K L at h
    rw [dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hSetS : PinchedHom.withLast K =
      (Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc ≤ ·) := by
    change PinchedHom.withLast (Finset.univ.filter (i.succ ≤ ·)) = _
    rw [dgCoherentBarWithLast_filter_left_le, dgCoherentBar_withLast_univ]
  have hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card := by
    rw [dgCoherentBarJoinSubset_card, hc]
    dsimp only [L]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (i.castAdd m).succ.castSucc =
      (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ) := by
    apply le_antisymm
    · have hf : ∀ x ∈ dgCoherentBarJoinSubset K L, (i.castAdd m).succ.castSucc ≤ x := by
        intro x hx
        rw [hSetT] at hx
        exact (Finset.mem_filter.mp hx).2
      exact hf _ ((dgCoherentBarJoinSubset K L).min'_mem (Index.nonempty hJ))
    · apply Finset.min'_le
      rw [hSetT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hb : Fin.last (n + m + 1) =
      (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSetT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.le_last _⟩
    · exact Fin.le_last _
  let k : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    ((i.castAdd m).succ.castSucc ≤ ·)).card : ℤ)
  have hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ) := by rw [hSetT]
  have hdS : - (r : ℤ) =
      2 - (((Finset.univ : Finset (Fin (n + 2))).filter
        (i.succ.castSucc ≤ ·)).card : ℤ) := by
    rw [← hSetS, PinchedHom.card_withLast, hc]
    push_cast
    omega
  have hF := dgCoherentBarCoconeLiftSimplex_mixed_factorization R D F hMC
    (r := r) (l := m) c s K L hc (by simp [L]) hK (i.castAdd m).succ.castSucc
    (Fin.last (n + m + 1)) k hJ ha hb hk
  simp only [L] at hF
  rw [dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at hF
  have hS : HEq (S.hom (PinchedHom.withLast K) (K.min' hK).castSucc
      (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
      (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
      (by rw [PinchedHom.card_withLast, hc]; push_cast; omega))
      (dgCoherentBarFullRight S i) :=
    SimplexData.hom_heq_of_indices_degree S hSetS (by rw [← hm]) rfl hdS
  have hx : S.obj (K.min' hK).castSucc = S.obj i.succ.castSucc := by rw [← hm]
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx rfl rfl hdS rfl
    (show -(m : ℤ) - (r : ℤ) =
      (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
        (i.succ.castSucc ≤ ·)).card : ℤ)) + -(m : ℤ) by rw [← hdS]; omega)
    (dgCoherentBarCoconeLiftHomAt R D F hMC c s)
    (S.hom (PinchedHom.withLast K) (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ))
      (PinchedHom.two_withLast hK) (PinchedHom.min_withLast hK _)
      (PinchedHom.max_withLast K _) (by rw [PinchedHom.card_withLast, hc]; push_cast; omega))
    (dgCoherentBarCoconeLiftHomAt R D F hMC c s) (dgCoherentBarFullRight S i)
    HEq.rfl hS (by omega) rfl
  refine HEq.trans ?_ (hF.trans hComp)
  exact SimplexData.hom_heq_of_indices_degree T hSetT.symm rfl rfl rfl

end SerrePositivity.InfinityCategories
