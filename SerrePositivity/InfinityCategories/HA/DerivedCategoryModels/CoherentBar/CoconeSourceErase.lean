module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyFactorization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPointIndex
/-!
概要：混合 HA 項で元の内部頂点を消した成分は、高次 Hom による native 削除成分の後合成。
方針：削除した先頭集合と全パラメーターの混合因数分解を適用する。
規約：内部頂点が存在する任意の次数で、端点と次数を異種等号で保持する。
使われ方：元の単体側の HA 項と Hom の Leibniz 項の一項ごとの比較。
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
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyFullErase_source {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) (i : Fin n) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (i.castAdd m))
      (compose R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y c s)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
        (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ.erase i.succ
  have hn : 0 < n := by have := i.isLt; omega
  have hc : K.card = n := by simp [K]
  have hr : K.card = (n - 1) + 1 := by omega
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  have h0K : (0 : Fin (n + 1)) ∈ K :=
    Finset.mem_erase.mpr ⟨ne_of_lt (Fin.succ_pos i), Finset.mem_univ _⟩
  have hm : K.min' hK = 0 :=
    le_antisymm (Finset.min'_le K 0 h0K) (Fin.zero_le _)
  have hSetT : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin (m + 1))) =
      (Finset.univ : Finset (Fin (n + m + 1 + 1))).erase (i.castAdd m).succ.castSucc := by
    change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ.erase i.succ) Finset.univ = _
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_erase_left, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ]
    rfl
  have hSetS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K =
      (Finset.univ : Finset (Fin (n + 2))).erase i.succ.castSucc := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (Finset.univ.erase i.succ) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarWithLast_erase, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ]
  have hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K
      (Finset.univ : Finset (Fin (m + 1)))).card := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hc, Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (0 : Fin (n + m + 1 + 1)) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K
        (Finset.univ : Finset (Fin (m + 1)))).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    have h0 : (0 : Fin (n + m + 1 + 1)) ∈
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin (m + 1))) := by
      rw [hSetT]
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos (i.castAdd m))),
          Finset.mem_univ _⟩
    exact le_antisymm (Fin.zero_le _)
      (Finset.min'_le _ 0 h0)
  have hb : Fin.last (n + m + 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K
        (Finset.univ : Finset (Fin (m + 1)))).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    have hl : Fin.last (n + m + 1) ∈
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin (m + 1))) := by
      rw [hSetT]
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩
    exact le_antisymm (Finset.le_max' _ _ hl) (Fin.le_last _)
  have hk : -((n + m : ℕ) : ℤ) + 1 =
      2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin (m + 1)))).card : ℤ) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hc, Finset.card_univ, Fintype.card_fin]
    push_cast
    omega
  have hF := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_mixed_factorization R D F hMC y
    (r := n - 1) (l := m) c s
    K (Finset.univ : Finset (Fin (m + 1))) hr (by simp) hK 0 (Fin.last (n + m + 1))
    (-((n + m : ℕ) : ℤ) + 1) hJ ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at hF
  have hT : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase T (i.castAdd m))
      (T.hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (Finset.univ : Finset (Fin (m + 1))))
        0 (Fin.last (n + m + 1))
        (-((n + m : ℕ) : ℤ) + 1) hJ ha hb hk) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSetT.symm rfl rfl rfl
  have hS : HEq (S.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K) (K.min' hK).castSucc
      (Fin.last (n + 1)) (-((n - 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hK)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hK _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast K _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hr]; push_cast; omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase S i) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree S hSetS
      (by rw [hm]; rfl) rfl (by omega)
  have hx : S.obj (K.min' hK).castSucc = S.obj 0 := by rw [hm]; rfl
  have hComp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx rfl rfl (show -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 by omega) rfl
    (show -(m : ℤ) - ((n - 1 : ℕ) : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y c s)
    (S.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast K) (K.min' hK).castSucc (Fin.last (n + 1))
      (-((n - 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hK)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hK _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast K _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, hr]; push_cast; omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y c s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase S i)
    HEq.rfl hS (by omega) (by omega)
  exact hT.trans (hF.trans hComp)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
