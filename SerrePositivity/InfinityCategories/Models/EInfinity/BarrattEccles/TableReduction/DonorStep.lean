module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExclusionEquivalence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows

/-!
模型。文献の定義との比較は後で
# 最終出現を早く除外した削除行の比較

概要：Berger–Fresse §1.4.4 の行長移動で短くする行の出力と除外状態を計算する。
方針：利用可能な行を削除値の前後で分け、先に除外した値を飛ばす。
規約：削除値は選択行の内部にあり、元の利用可能行には重複しない。
使われ方：相殺相手の削除行通過後に二つの抽出状態を合流させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：一文字を除外することは利用可能行からその値を除くこと（BF §1.4.4）。
方針：二つの filter の条件を同じ論理積として比較する。
規約：元の状態に既にその値があっても成立する。
使われ方：受け取り行で早く除外した値の削除行への影響を計算する。 -/
lemma available_append_singleton (removed row : List α) (a : α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).filter (fun x => x ≠ a) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hr : x ∈ removed <;> by_cases ha : x = a <;>
    simp [List.mem_append, hr, ha]

/-- 概要：属さない値を除く filter は元のリストを保つ（BF §1.4.4）。
方針：全ての所属要素に対して不等号を確認する。
規約：リストの重複を要求しない。
使われ方：削除値の前後の部分が変わらないことを示す。 -/
lemma filter_ne_eq_self_of_not_mem (xs : List α) (a : α) (ha : a ∉ xs) :
    xs.filter (fun x => x ≠ a) = xs := by
  apply List.filter_eq_self.mpr
  intro x hx
  simp only [decide_eq_true_eq]
  intro he
  subst x
  exact ha hx

/-- 概要：削除値を先に除外すると利用可能行からその一文字だけが消える（BF §1.4.4）。
方針：削除値の前後は filter で不変であることを使う。
規約：利用可能行を pre ++ a :: post と指定し、他には a がない。
使われ方：短くする行の抽出長を 1 減らした後の出力を計算する。 -/
lemma available_donor_split (removed row pre post : List α) (a : α)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row = pre ++ post := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_append_singleton, he, List.filter_append]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_ne_eq_self_of_not_mem pre a hpre]
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_ne_eq_self_of_not_mem post a hpost]

/-- 概要：短い削除行の出力は元の選択行の削除値だけを除いたもの（BF §1.4.4）。
方針：利用可能行の前後分割に take の連結公式を適用する。
規約：削除値より後に s 文字を選ぶ。
使われ方：相殺する二つの削除後出力を比較する局所公式。 -/
lemma donor_selected_split (removed row pre post : List α) (a : α) (s : ℕ)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s) = pre ++ post.take s ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (pre.length + (s + 1)) = pre ++ a :: post.take s := by
  constructor
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_donor_split removed row pre post a he hpre hpost,
      List.take_length_add_append]
  · rw [he, List.take_length_add_append, List.take_succ_cons]

/-- 概要：削除値を早く除外して行長を減らすと行通過後の除外所属は元と同じ（BF §1.4.4）。
方針：削除値の追加順序だけが変わることを take の公式で示す。
規約：s は正で、削除値は末尾以外に選択される。
使われ方：後続の全 table の抽出を除外所属の同値で一致させる。 -/
lemma donor_exclusion_equiv (removed row pre post : List α) (a : α) (s : ℕ)
    (hs : 0 < s) (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post)
    (hpre : a ∉ pre) (hpost : a ∉ post) (x : α) :
    x ∈ (removed ++ [a]) ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1) ↔
      x ∈ removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (pre.length + (s + 1) - 1) := by
  have hshort : pre.length + s - 1 = pre.length + (s - 1) := by omega
  have hlong : pre.length + (s + 1) - 1 = pre.length + ((s - 1) + 1) := by omega
  rw [hshort, hlong, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_selected_split removed row pre post a (s - 1) he hpre hpost).1,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_selected_split removed row pre post a (s - 1) he hpre hpost).2]
  simp only [List.mem_append, List.mem_cons]
  tauto

/-- 概要：削除値を早く除外した短い行は同じ後続抽出へ合流する（BF §1.4.4）。
方針：削除行の選択出力と除外状態の同値を reduceRows の再帰へ適用する。
規約：元の選択行で削除値より後に少なくとも一文字を選ぶ。
使われ方：相殺候補の削除行から後の抽出を実際に再構成する。 -/
lemma reduceRows_donor_step (removed row pre post : List α) (a : α) (s : ℕ)
    (hs : 0 < s) (hb : s ≤ post.length)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (pre.length + (s + 1) - 1)) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, pre.length + s) :: rest) (removed ++ [a]) =
      some ((pre ++ post.take s) ++ tail) := by
  have hstate := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest
    ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1))
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (pre.length + (s + 1) - 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_exclusion_equiv removed row pre post a s hs he hpre hpost)
  have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1)) =
        some tail := hstate.trans ht
  have hbound : pre.length + s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).length := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_donor_split removed row pre post a he hpre hpost, List.length_append]
    omega
  have hsuccess := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (pre.length + s) rest (removed ++ [a])
    tail (by omega) hbound htail
  rw [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_selected_split removed row pre post a s he hpre hpost).1] at hsuccess
  exact hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
