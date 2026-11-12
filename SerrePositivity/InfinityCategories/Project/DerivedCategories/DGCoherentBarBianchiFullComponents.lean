module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiFullTerms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarPrefixComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedCuts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

/-!
概要：全体 HA 右辺の各削除・右切断の成分を、同じ bar の実包含へ戻す。
方針：最終点を含む集合の削除・切断を先頭集合へ移し、元の係数比較を適用する。
規約：有効な端点と次数の任意の指定を保持する。
使われ方：元の θ の各面・prefix 列との項別照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_full_deleted {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (k : ℤ)
    (hE : 2 ≤ ((Finset.univ : Finset (Fin (n + 3))).erase i.succ.castSucc).card)
    (ha : 0 = (Finset.univ.erase i.succ.castSucc).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hb : Fin.last (n + 2) = (Finset.univ.erase i.succ.castSucc).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hk : k = 2 - ((Finset.univ.erase i.succ.castSucc).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).hom (Finset.univ.erase i.succ.castSucc)
      0 (Fin.last (n + 2)) k hE ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ)) := by
  let J := (Finset.univ : Finset (Fin (n + 2))).erase i.succ
  have hJ : J.Nonempty := Finset.card_pos.mp (by simp [J])
  have hm : J.min' hJ = 0 :=
    (J.isLeast_min' hJ).unique ⟨by simp [J]; exact ne_of_lt (Fin.succ_pos i), fun j _ => Fin.zero_le j⟩
  have hs : (Finset.univ : Finset (Fin (n + 3))).erase i.succ.castSucc =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.erase_withLast]
  refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_face_coefficient R D F σ i.succ hJ)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ hs (by rw [hm]; rfl) rfl (by
    have hcard : (Finset.univ.erase i.succ.castSucc : Finset (Fin (n + 3))).card = n + 2 := by simp
    rw [hcard] at hk
    omega)

lemma dgCoherentBarBianchiData_full_right {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (k : ℤ)
    (hE : 2 ≤ ((Finset.univ : Finset (Fin (n + 3))).filter (i.succ.castSucc ≤ ·)).card)
    (ha : i.succ.castSucc = (Finset.univ.filter (i.succ.castSucc ≤ ·)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hb : Fin.last (n + 2) = (Finset.univ.filter (i.succ.castSucc ≤ ·)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hk : k = 2 - ((Finset.univ.filter (i.succ.castSucc ≤ ·)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).hom (Finset.univ.filter (i.succ.castSucc ≤ ·))
      i.succ.castSucc (Fin.last (n + 2)) k hE ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (i.val + 1) (by omega))) := by
  let J := (Finset.univ : Finset (Fin (n + 2))).filter (i.succ ≤ ·)
  have hJ : J.Nonempty := ⟨i.succ, by simp [J]⟩
  have hm : J.min' hJ = i.succ :=
    (J.isLeast_min' hJ).unique ⟨by simp [J], fun j hj => (Finset.mem_filter.mp hj).2⟩
  have hs : (Finset.univ : Finset (Fin (n + 3))).filter (i.succ.castSucc ≤ ·) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.right_withLast]
  have hcard : (Finset.univ.filter (i.succ.castSucc ≤ ·) : Finset (Fin (n + 3))).card =
      (n + 1 - i.succ.val) + 2 := by
    rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]
    change ((Finset.univ : Finset (Fin (n + 2))).filter (i.succ ≤ ·)).card + 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail_card]
  refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_tail_coefficient R D F σ i.succ hJ)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ hs (by rw [hm]) rfl (by
    rw [hcard] at hk
    omega)


lemma dgCoherentBarBianchiData_full_left {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (k : ℤ)
    (hE : 2 ≤ ((Finset.univ : Finset (Fin (n + 3))).filter (· ≤ i.succ.castSucc)).card)
    (ha : 0 = (Finset.univ.filter (· ≤ i.succ.castSucc)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hb : i.succ.castSucc = (Finset.univ.filter (· ≤ i.succ.castSucc)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE))
    (hk : k = 2 - ((Finset.univ.filter (· ≤ i.succ.castSucc)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).hom (Finset.univ.filter (· ≤ i.succ.castSucc))
      0 i.succ.castSucc k hE ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F σ i.val (by omega)) := by
  let J := (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ i.succ)
  have hcardJ : J.card = i.val + 2 := by
    have hj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_card (n + 1) i.succ
    simpa only [Fin.val_succ, Nat.add_assoc] using hj
  have h2 : 2 ≤ J.card := by rw [hcardJ]; omega
  have hm : J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty h2) = 0 :=
    (J.isLeast_min' _).unique ⟨by simp [J], fun j _ => Fin.zero_le j⟩
  have hbJ : i.succ = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty h2) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max (Finset.mem_univ _) _
  have hkJ : -(i.val : ℤ) = 2 - (J.card : ℤ) := by rw [hcardJ]; omega
  have hs : (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ i.succ.castSucc) =
      J.image Fin.castSucc := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.left_withLast]
  have hcard : (Finset.univ.filter (· ≤ i.succ.castSucc) : Finset (Fin (n + 3))).card =
      i.val + 2 := by rw [hs, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hcardJ
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_hom_front R D F σ J 0 i.succ (-(i.val : ℤ)) h2 hm.symm hbJ hkJ
  have hr : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).hom J 0 i.succ (-(i.val : ℤ)) h2 hm.symm hbJ hkJ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixRawComponent R D F σ i.val (by omega)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixRawComponent
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder_image (n + 1) i.succ).symm rfl rfl rfl
  refine HEq.trans ?_ (hh.trans (hr.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom_heq_rawComponent R D F σ i.val (by omega)).symm))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ hs rfl rfl (by rw [hcard] at hk; omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
