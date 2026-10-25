module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterErase
/-!
概要：逆構成の最後のパラメーター切断の左因子を、最後の標準面の高次 Hom と native 列へ分解する。
方針：最後の点を除いたパラメーター集合の混合因数分解を使う。
規約：実際の HA 成分を用い、端点と次数を異種等号で保持する。
使われ方：定値側の単位で残る最後の切断合成を最終面へ戻す。
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
  (N : RightModule R D)

lemma dgCoherentBarInverseFullLeft_parameter_last {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    HEq (dgCoherentBarFullLeft
      (dgCoherentBarInverseRawData R D F hMC N f s) ((Fin.last m).natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := N)
        (dgCoherentBarInverseFaceHom R D F hMC N f (Fin.last (m + 1)))
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl) := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
  let K : Finset (Fin (n + 1)) := Finset.univ
  let L : Finset (Fin (m + 2)) := Finset.univ.erase (Fin.last (m + 1))
  let j := ((Fin.last m).natAdd n).succ.castSucc
  have hcL : L.card = m + 1 := by simp [L]
  have hj : dgCoherentBarJoinRight n (m + 1) (Fin.last m).castSucc = j :=
    Fin.ext (by change n + 1 + m = n + m + 1; omega)
  have hSet : dgCoherentBarJoinSubset K L =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter (· ≤ j) := by
    have h := dgCoherentBarJoinSubset_filter_le_right K
      (Finset.univ : Finset (Fin (m + 2))) (Fin.last m).castSucc
    simp only [K] at h
    rw [dgCoherentBarJoinSubset_univ, hj, ← dgCoherentBarUniv_erase_last] at h
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
  have hb : j = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
    · apply Finset.max'_le
      intro x hx
      rw [hSet] at hx
      exact (Finset.mem_filter.mp hx).2
  let k : ℤ := 2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
    (· ≤ j)).card : ℤ)
  have hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ) := by rw [hSet]
  have hF := dgCoherentBarInverseRawData_mixed_factorization R D F hMC N
    (r := n) (l := m) f s K L (by simp [K]) hcL Finset.univ_nonempty
    0 j k hJ ha hb hk
  simp only [K, L] at hF
  have hx := dgCoherentBarNativeSimplex_subset_source R D F hMC s Finset.univ n
    (by simp) Finset.univ_nonempty
  rw [dgCoherentBarSubsetLabel_univ] at hx
  have hS := dgCoherentBarNativeSimplex_subset_hom_heq R D F hMC s Finset.univ n
    (by simp) Finset.univ_nonempty
  rw [dgCoherentBarSubsetLabel_univ] at hS
  have hComp := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx (dgCoherentBarNativeSimplex_last R D F hMC s) rfl rfl rfl
    (p := -(n : ℤ)) (q := -(m : ℤ)) (k := -(m : ℤ) - (n : ℤ))
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -(n : ℤ) + -(m : ℤ))
    (show -(m : ℤ) - (n : ℤ) = -(n : ℤ) + -(m : ℤ) by omega)
    _ _ (dgCoherentBarInverseFaceHom R D F hMC N f (Fin.last (m + 1)))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (dgCoherentBarInverseFaceHomAt_heq R D F hMC N f (Fin.last (m + 1)) s) hS (by omega) rfl
  refine HEq.trans ?_ (hF.trans hComp)
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories
