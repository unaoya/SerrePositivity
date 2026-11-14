module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanUnknownIndex

/-! # span の未知集合の端点・濃度・切断

概要：可変頂点集合の端点と濃度、および Bianchi 計算で消える集合を記録する。
方針：後続集合を二以上の終区間として扱い、削除・切断が欠く頂点を指定する。
規約：先頭二点は固定。使われ方：D7 の未知成分の次数と脚側の残差計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 概要：可変頂点集合の最初の点。
方針：固定二点の次の番号を取る。
規約：零次元でも値は二。使われ方：cofiber の余錐頂点。 -/
def spanApex (n : ℕ) : Fin (n + 4) := ⟨2, by omega⟩

/-- 概要：後続集合の所属は余錐頂点以上であることと同値。
方針：所属の自然数の下界を有限順序集合の順序で読む。
規約：上界は型に含む。使われ方：切断の既知性。 -/
lemma mem_spanSuffixFaces_iff_le {n : ℕ} (i : Fin (n + 4)) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ↔ spanApex n ≤ i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces i

/-- 概要：可変頂点の集合の濃度は n+2。
方針：二回の succ の単射性で像の濃度を計算する。
規約：全次元。使われ方：未知の射の次数。 -/
lemma card_spanSuffixFaces (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card = n + 2 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    apply Fin.ext
    have hv := congrArg (fun z : Fin (n + 4) => z.val) h
    change i.val + 1 + 1 = j.val + 1 + 1 at hv
    omega

/-- 概要：可変頂点集合の最小元は余錐頂点。
方針：終区間の下界とその所属を使う。
規約：集合は非空。使われ方：未知成分の始点。 -/
lemma spanSuffixFaces_min (n : ℕ) (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).Nonempty) :
    spanApex n = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' h :=
  (show IsLeast ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n : Finset _) : Set (Fin (n + 4))) (spanApex n) from
    ⟨(mem_spanSuffixFaces_iff_le _).mpr le_rfl,
      fun i hi => (mem_spanSuffixFaces_iff_le i).mp hi⟩).unique
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).isLeast_min' h)

/-- 概要：可変頂点集合の最大元は最後の頂点。
方針：最後の点の所属と全ての有限添字の上界を使う。
規約：全次元。使われ方：未知成分の共通終点。 -/
lemma spanSuffixFaces_max (n : ℕ) (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).Nonempty) :
    Fin.last (n + 3) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' h :=
  (show IsGreatest ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n : Finset _) : Set (Fin (n + 4))) (Fin.last (n + 3)) from
    ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega),
      fun i _ => Fin.le_last i⟩).unique ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).isGreatest_max' h)

/-- 概要：余錐頂点は最後の頂点より小さい。
方針：値二と n+3 を比較する。
規約：n=0 を含む。使われ方：Bianchi の内部点。 -/
lemma spanApex_lt_last (n : ℕ) : spanApex n < Fin.last (n + 3) := by
  change 2 < n + 3
  omega

/-- 概要：可変頂点を削除した集合は既知集合。
方針：削除した頂点の不在を使う。
規約：元の集合は任意。使われ方：削除残差の消去。 -/
lemma span_erase_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I.erase j := by
  intro h
  exact Finset.notMem_erase j I (h hj)

/-- 概要：最後の頂点より前で終わる左切断は既知集合。
方針：最後の可変頂点を含まないことを使う。
規約：元の集合は任意。使われ方：左切断の残差の消去。 -/
lemma span_leftCut_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : j < Fin.last (n + 3)) :
    ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I.filter (· ≤ j) := by
  intro h
  have hm := h ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces (Fin.last (n + 3))).mpr (by change 2 ≤ n + 3; omega))
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

/-- 概要：余錐頂点より後で始まる右切断は既知集合。
方針：最初の可変頂点を含まないことを使う。
規約：元の集合は任意。使われ方：右切断の残差の消去。 -/
lemma span_rightCut_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : spanApex n < j) :
    ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I.filter (j ≤ ·) := by
  intro h
  have hm := h ((mem_spanSuffixFaces_iff_le (spanApex n)).mpr le_rfl)
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
