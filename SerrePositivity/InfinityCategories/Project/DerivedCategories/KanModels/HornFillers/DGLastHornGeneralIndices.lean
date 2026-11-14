module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # 任意次元の最後外ホーンの欠面の端点と cochain 次数

概要：次元 n+2 の欠面の有限集合・最後から二番目の頂点・二未知の次数を固定する。
方針：全体集合から最後の頂点を除き、min・max・濃度を直接検証する。
規約：n=0 も含む。使われ方：一般の最後外ホーンの二未知残差と実充填。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 最後外ホーンの最後から二番目の頂点。 -/
def dgLastHornPenultimate (n : ℕ) : Fin (n + 3) := (Fin.last (n + 1)).castSucc

/-- 次元 n+2 の最後外ホーンの欠けた面の頂点集合。 -/
def dgLastHornMissingIndex (n : ℕ) : Finset (Fin (n + 3)) :=
  Finset.univ.erase (Fin.last (n + 2))

/-- 欠面に入るのは、最後の頂点以外の全頂点。 -/
lemma dgLastHornMissingIndex_mem {n : ℕ} (i : Fin (n + 3)) :
    i ∈ dgLastHornMissingIndex n ↔ i ≠ Fin.last (n + 2) := by
  simp only [dgLastHornMissingIndex, Finset.mem_erase, Finset.mem_univ, and_true]

/-- 欠面は全体集合と異なる。 -/
lemma dgLastHornMissingIndex_ne_univ (n : ℕ) : dgLastHornMissingIndex n ≠ Finset.univ := by
  intro he
  have hm : Fin.last (n + 2) ∈ dgLastHornMissingIndex n := he.symm ▸ Finset.mem_univ _
  exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hm

/-- 欠面の頂点数は n+2。 -/
lemma dgLastHornMissingIndex_card (n : ℕ) : (dgLastHornMissingIndex n).card = n + 2 := by
  simp [dgLastHornMissingIndex]

/-- 欠面は二頂点以上を持つ。 -/
lemma dgLastHornMissingIndex_two (n : ℕ) : 2 ≤ (dgLastHornMissingIndex n).card := by
  rw [dgLastHornMissingIndex_card]
  omega

/-- 欠面の始頂点は零。 -/
lemma dgLastHornMissingIndex_min (n : ℕ) :
    (0 : Fin (n + 3)) = (dgLastHornMissingIndex n).min'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (dgLastHornMissingIndex_two n)) := by
  symm
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨(dgLastHornMissingIndex_mem _).mpr ?_, fun i _ => Fin.zero_le i⟩
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

/-- 欠面の終頂点は、最後から二番目の頂点。 -/
lemma dgLastHornMissingIndex_max (n : ℕ) :
    dgLastHornPenultimate n = (dgLastHornMissingIndex n).max'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (dgLastHornMissingIndex_two n)) := by
  symm
  apply (Finset.max'_eq_iff _ _ _).mpr
  refine ⟨(dgLastHornMissingIndex_mem _).mpr (Fin.castSucc_ne_last _), ?_⟩
  intro i hi
  have hn := (dgLastHornMissingIndex_mem i).mp hi
  have hv : i.val ≠ n + 2 := by
    intro he
    exact hn (Fin.ext he)
  apply Fin.le_iff_val_le_val.mpr
  change i.val ≤ n + 1
  have hb := i.is_lt
  omega

/-- 欠面 cochain Q の次数は −n。 -/
lemma dgLastHornMissingIndex_degree (n : ℕ) :
    -(n : ℤ) = 2 - ((dgLastHornMissingIndex n).card : ℤ) := by
  rw [dgLastHornMissingIndex_card]
  push_cast
  ring

/-- 最上位 cochain A の次数は −n−1。 -/
lemma dgLastHornTop_degree (n : ℕ) :
    -(n : ℤ) - 1 = 2 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ) := by
  rw [Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- 最上位の全体集合も二頂点以上を持つ。 -/
lemma dgLastHornTop_two (n : ℕ) :
    2 ≤ (Finset.univ : Finset (Fin (n + 3))).card := by
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- 全体集合の始頂点は零。 -/
lemma dgLastHornTop_min (n : ℕ) :
    (0 : Fin (n + 3)) = (Finset.univ : Finset (Fin (n + 3))).min'
      (by simp : (Finset.univ : Finset (Fin (n + 3))).Nonempty) := by
  symm
  exact (Finset.min'_eq_iff _ _ _).mpr ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩

/-- 全体集合の終頂点は最後の頂点。 -/
lemma dgLastHornTop_max (n : ℕ) :
    Fin.last (n + 2) = (Finset.univ : Finset (Fin (n + 3))).max'
      (by simp : (Finset.univ : Finset (Fin (n + 3))).Nonempty) := by
  symm
  exact (Finset.max'_eq_iff _ _ _).mpr ⟨Finset.mem_univ _, fun i _ => Fin.le_last i⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
