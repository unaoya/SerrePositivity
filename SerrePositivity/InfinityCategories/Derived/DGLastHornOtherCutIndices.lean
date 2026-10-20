module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornLastCutIndices

/-! # 最後以外の内部頂点の切断は既知集合

概要：右切断・内部頂点削除は欠面でなく、左切断が欠面なら頂点は最後内部頂点。
方針：最後頂点と零頂点の所属、欠面の最大元を使う。
規約：全次元。使われ方：Bianchi の最後以外の寄与の消去。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories
variable {n : ℕ} (j : Fin (n + 3))

/-- 内部頂点への左切断は、最後頂点を含まないため全体集合でない。 -/
lemma dgLastHornLeftCut_ne_univ (hj : j < Fin.last (n + 2)) :
    (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ j) ≠ Finset.univ := by
  intro he
  have hm : Fin.last (n + 2) ∈ (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ j) :=
    he.symm ▸ Finset.mem_univ _
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

/-- 内部頂点からの右切断は、零頂点を含まないため全体集合でない。 -/
lemma dgLastHornRightCut_ne_univ (hj : (0 : Fin (n + 3)) < j) :
    (Finset.univ : Finset (Fin (n + 3))).filter (j ≤ ·) ≠ Finset.univ := by
  intro he
  have hm : (0 : Fin (n + 3)) ∈ (Finset.univ : Finset (Fin (n + 3))).filter (j ≤ ·) :=
    he.symm ▸ Finset.mem_univ _
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

/-- 一頂点削除は全体集合と異なる。 -/
lemma dgLastHornErase_ne_univ :
    (Finset.univ : Finset (Fin (n + 3))).erase j ≠ Finset.univ := by
  intro he
  exact (Finset.notMem_erase j Finset.univ) (he.symm ▸ Finset.mem_univ j)

/-- 内部頂点からの右切断は、最後頂点を含むため欠面でない。 -/
lemma dgLastHornRightCut_ne_missing (hj : j < Fin.last (n + 2)) :
    (Finset.univ : Finset (Fin (n + 3))).filter (j ≤ ·) ≠ dgLastHornMissingIndex n := by
  intro he
  have hm : Fin.last (n + 2) ∈ dgLastHornMissingIndex n :=
    he ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.le⟩
  exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hm

/-- 内部頂点削除も、最後頂点を含むため欠面でない。 -/
lemma dgLastHornErase_ne_missing (hj : j < Fin.last (n + 2)) :
    (Finset.univ : Finset (Fin (n + 3))).erase j ≠ dgLastHornMissingIndex n := by
  intro he
  have hm : Fin.last (n + 2) ∈ dgLastHornMissingIndex n :=
    he ▸ Finset.mem_erase.mpr ⟨(ne_of_lt hj).symm, Finset.mem_univ _⟩
  exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hm

/-- 最後内部頂点以外への左切断は欠面と異なる。 -/
lemma dgLastHornLeftCut_ne_missing (hj : j ≠ dgLastHornPenultimate n) :
    (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ j) ≠ dgLastHornMissingIndex n := by
  intro he
  have hmj : j ∈ dgLastHornMissingIndex n :=
    he ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hjp : j ≤ dgLastHornPenultimate n :=
    (Finset.le_max' (dgLastHornMissingIndex n) j hmj).trans_eq (dgLastHornMissingIndex_max n).symm
  have hmp : dgLastHornPenultimate n ∈ dgLastHornMissingIndex n :=
    (dgLastHornMissingIndex_mem _).mpr (ne_of_lt (dgLastHornPenultimate_lt_last n))
  have hmp' : dgLastHornPenultimate n ∈
      (Finset.univ : Finset (Fin (n + 3))).filter (· ≤ j) := he.symm ▸ hmp
  have hpj : dgLastHornPenultimate n ≤ j := (Finset.mem_filter.mp hmp').2
  exact hj (le_antisymm hjp hpj)

end SerrePositivity.InfinityCategories
