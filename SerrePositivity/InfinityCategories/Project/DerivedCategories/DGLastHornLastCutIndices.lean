module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralIndices

/-! # 最後内部頂点による切断の有限集合

概要：全体集合の最後の切断は、欠面・最後辺の二点・最後頂点の一点に分かれる。
方針：最後から二番目の頂点と最後頂点の間の有限順序を直接検査する。
規約：全次元 n+2。使われ方：一般最上位 rhs の一寄与の分解。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 最後から二番目の頂点は零より大きい。 -/
lemma dgLastHornPenultimate_pos (n : ℕ) : (0 : Fin (n + 3)) < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n := by
  change 0 < n + 1
  omega

/-- 最後から二番目の頂点は最後頂点より小さい。 -/
lemma dgLastHornPenultimate_lt_last (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n < Fin.last (n + 2) := Fin.castSucc_lt_last _

/-- 最後内部頂点への左切断は、同じ欠面の頂点集合。 -/
lemma dgLastHornLastCut_left (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_mem]
  constructor
  · intro hi he
    exact not_le_of_gt (dgLastHornPenultimate_lt_last n) (he ▸ hi)
  · intro hi
    have hm := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_mem i).mpr hi
    have hl := Finset.le_max' (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) i hm
    exact hl.trans_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n).symm

/-- 最後内部頂点からの右切断は、最後の二頂点だけ。 -/
lemma dgLastHornLastCut_right (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 3))).filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n ≤ ·) =
      {_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n, Fin.last (n + 2)} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hi
    change n + 1 ≤ i.val at hi
    have hb := i.is_lt
    have hv : i.val = n + 1 ∨ i.val = n + 2 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rintro (rfl | rfl)
    · exact le_rfl
    · exact (dgLastHornPenultimate_lt_last n).le

/-- 最後内部頂点より厳密に大きいのは、最後頂点だけ。 -/
lemma dgLastHornLastCut_upper (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 3))).filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n < ·) =
      {Fin.last (n + 2)} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    change n + 1 < i.val at hi
    have hb := i.is_lt
    apply Fin.ext
    change i.val = n + 2
    omega
  · rintro rfl
    exact dgLastHornPenultimate_lt_last n

/-- 符号の指数となる厳密上側の濃度は一。 -/
lemma dgLastHornLastCut_upper_card (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 3))).filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n < ·)).card = 1 := by
  rw [dgLastHornLastCut_upper, Finset.card_singleton]

/-- 最後の右切断の二点集合は、欠面と異なる。 -/
lemma dgLastHornLastCut_right_ne_missing (n : ℕ) :
    {_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n, Fin.last (n + 2)} ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n := by
  intro he
  have hm : Fin.last (n + 2) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n := he ▸ (by simp)
  exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hm

/-- 最後内部頂点を削除した集合も、欠面と異なる。 -/
lemma dgLastHornLastCut_erase_ne_missing (n : ℕ) :
    Finset.univ.erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n := by
  intro he
  have hm : Fin.last (n + 2) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n :=
    he ▸ Finset.mem_erase.mpr ⟨(ne_of_lt (dgLastHornPenultimate_lt_last n)).symm,
      Finset.mem_univ _⟩
  exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
