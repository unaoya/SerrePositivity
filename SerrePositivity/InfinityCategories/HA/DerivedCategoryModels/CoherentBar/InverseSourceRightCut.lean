module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceErase
/-!
概要：逆構成の元の内部頂点で切った混合 HA の右因子を、高次 Hom と native の右因子へ分解する。
方針：末尾の先頭集合と全パラメーターの混合因数分解を適用する。
規約：全整数次数の実加群 Hom と同じ Koszul 合成を使う。
使われ方：混合 HA 切断合成を、native HA 項の後合成へ直す。
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

lemma dgCoherentBarInverseFullRight_source {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (i : Fin n) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (i.castAdd m))
      (compose R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHomAt R D F hMC N f s)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
        rfl) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s)
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ.filter (i.succ ≤ ·)
  let L : Finset (Fin (m + 1)) := Finset.univ
  let r := n - (i.val + 1)
  have hc : K.card = r + 1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail_card n i.succ
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  have hm : i.succ = K.min' hK := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min (Finset.mem_univ _) hK
  have hSetT : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L =
      (Finset.univ : Finset (Fin (n + m + 2))).filter
        ((i.castAdd m).succ.castSucc ≤ ·) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_left_le
      (Finset.univ : Finset (Fin (n + 1))) L i.succ
    change _ = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L at h
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hSetS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K =
      (Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc ≤ ·) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (Finset.univ.filter (i.succ ≤ ·)) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarWithLast_filter_left_le, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ]
  have hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hc]
    dsimp only [L]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (i.castAdd m).succ.castSucc =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    apply le_antisymm
    · have hf : ∀ x ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L, (i.castAdd m).succ.castSucc ≤ x := by
        intro x hx
        rw [hSetT] at hx
        exact (Finset.mem_filter.mp hx).2
      exact hf _ ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    · apply Finset.min'_le
      rw [hSetT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hb : Fin.last (n + m + 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSetT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.le_last _⟩
    · exact Fin.le_last _
  let k : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    ((i.castAdd m).succ.castSucc ≤ ·)).card : ℤ)
  have hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ) := by rw [hSetT]
  have hdS : - (r : ℤ) =
      2 - (((Finset.univ : Finset (Fin (n + 2))).filter
        (i.succ.castSucc ≤ ·)).card : ℤ) := by
    rw [← hSetS, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hc]
    push_cast
    omega
  have hF := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_factorization R D F hMC N
    (r := r) (l := m) f s K L hc (by simp [L]) hK (i.castAdd m).succ.castSucc
    (Fin.last (n + m + 1)) k hJ ha hb hk
  simp only [L] at hF
  have hS : HEq (S.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K) (K.min' hK).castSucc
      (Fin.last (n + 1)) (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hK)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hK _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast K _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hc]; push_cast; omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight S i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree S hSetS (by rw [← hm]) rfl hdS
  have hx : S.obj (K.min' hK).castSucc = S.obj i.succ.castSucc := by rw [← hm]
  have hComp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx rfl rfl hdS rfl
    (show -(m : ℤ) - (r : ℤ) =
      (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
        (i.succ.castSucc ≤ ·)).card : ℤ)) + -(m : ℤ) by rw [← hdS]; omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHomAt R D F hMC N f s)
    (S.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K) (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hK) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hK _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast K _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hc]; push_cast; omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHomAt R D F hMC N f s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight S i)
    HEq.rfl hS (by omega) rfl
  refine HEq.trans ?_ (hF.trans hComp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSetT.symm rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
