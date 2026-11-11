module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterFaces
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceSum
/-!
概要：逆構成のパラメーターの内部頂点を消した混合 HA 成分を、標準面の高次 Hom へ同定する。
方針：全先頭集合と一点削除したパラメーター集合の因数分解を使う。
規約：正次数の任意の余錐族と零次元を含む任意の元の単体を扱う。
使われ方：混合 HA のパラメーター側の削除和を標準面の和へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
  (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)

lemma dgCoherentBarInverseFullErase_parameter {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
        (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
        (z := N)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHom R D F hMC N f j.castSucc)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s)
  let L : Finset (Fin (m + 2)) := Finset.univ.erase j.castSucc
  have hcL : L.card = m + 1 := by simp [L]
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hSet : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin (n + 1))) L =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).erase (j.natAdd n).succ.castSucc := by
    change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset Finset.univ (Finset.univ.erase j.castSucc) = _
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_erase_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj]
  let K : Finset (Fin (n + 1)) := Finset.univ
  have hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (0 : Fin (n + (m + 1) + 2)) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    have h0 : (0 : Fin (n + (m + 1) + 2)) ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L := by
      rw [hSet]
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos (j.natAdd n))),
          Finset.mem_univ _⟩
    exact le_antisymm (Fin.zero_le _) (Finset.min'_le _ 0 h0)
  have hb : Fin.last (n + (m + 1) + 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    have hl : Fin.last (n + (m + 1) + 1) ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L := by
      rw [hSet]
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩
    exact le_antisymm (Finset.le_max' _ _ hl) (Fin.le_last _)
  have hk : -((n + (m + 1) : ℕ) : ℤ) + 1 =
      2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    omega
  have hF := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_factorization R D F hMC N
    (r := n) (l := m) f s K L (by simp [K]) hcL Finset.univ_nonempty
    0 (Fin.last (n + (m + 1) + 1)) (-((n + (m + 1) : ℕ) : ℤ) + 1) hJ ha hb hk
  simp only [K, L] at hF
  have hx := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_subset_source R D F hMC s Finset.univ n
    (by simp) Finset.univ_nonempty
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_univ] at hx
  have hS := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_subset_hom_heq R D F hMC s Finset.univ n
    (by simp) Finset.univ_nonempty
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_univ] at hS
  have hComp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last R D F hMC s) rfl rfl rfl
    (p := -(n : ℤ)) (q := -(m : ℤ)) (k := -(m : ℤ) - (n : ℤ))
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (show -(m : ℤ) - (n : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)
    _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHom R D F hMC N f j.castSucc)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHomAt_heq R D F hMC N f j.castSucc s) hS (by omega) (by omega)
  refine HEq.trans ?_ (hF.trans hComp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
