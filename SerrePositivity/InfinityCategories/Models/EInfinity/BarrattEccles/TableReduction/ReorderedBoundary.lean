module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 前半の並べ替えで保存される行境界の重複

概要：Berger–Fresse §1.5.8 の外側ラベルで切った隣接合成行の退化を扱う。
方針：前半の所属集合が一致すれば、前行の除外が次行の前半を全て消す。
規約：除外リストと前半には重複を許し、境界文字は前半と除外の外に置く。
使われ方：逆方向の table 復元で、垂直な連続行の末尾を内側ラベルへ制限する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：前半の順序を変えても前行の除外後に境界文字が先頭に残る（BF §1.5.8）。
方針：次行の前半の各値は、既除外か今回の前半の可用値に属する。
規約：前半は同じ所属集合を持ち、境界文字 a はその外に置く。
使われ方：同じ外側置換を持つ二つの合成行の境界を比較する。 -/
lemma available_reordered_prefix (removed pre pre' : List α) (a : α) (post : List α)
    (hm : ∀ x, x ∈ pre' ↔ x ∈ pre) (ha : a ∉ pre) (har : a ∉ removed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre) (pre' ++ a :: post) =
      a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre) post := by
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre) pre' = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hx' := (hm x).mp hx
    by_cases hr : x ∈ removed <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, hr, hx']
  have har' : a ∉ removed ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre := by
    simp only [List.mem_append, not_or]
    exact ⟨har, fun h => ha (List.mem_of_mem_filter h)⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available] at har'
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append] at hp ⊢
  rw [hp]
  simp only [List.nil_append, List.filter_cons]
  exact ite_eq_left (decide_eq_true har')

/-- 概要：同じ前半集合の直後で切る成功二行の出力は退化（BF §1.5.8）。
方針：前行の末尾 a と次行の先頭 a を成功の再帰式から取り出す。
規約：次行の後半や残りの行には制限を置かない。
使われ方：非退化出力の垂直区間では外側文字を中間行末に選べない。 -/
lemma reduceRows_reordered_prefix_not_isChain (pre pre' : List α) (a : α)
    (post post' : List α) (hm : ∀ x, x ∈ pre' ↔ x ∈ pre)
    (ha : a ∉ pre) (removed out : List α) (har : a ∉ removed)
    (s : ℕ) (rest : List (List α × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((pre ++ a :: post, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre).length + 1) ::
        (pre' ++ a :: post', s) :: rest) removed = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre ++ a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed post := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, List.filter_cons,
      decide_eq_true har, ite_true]
  obtain ⟨_, _, tail, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  have hr : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post)).take
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre).length + 1 - 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre := by
    rw [he, Nat.add_sub_cancel, List.take_left]
  rw [hr] at ht
  obtain ⟨hs, _, tail', _, ho'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_reordered_prefix removed pre pre' a post' hm ha har] at ho'
  rw [he, List.take_append, Nat.add_sub_cancel_left] at ho
  simp only [List.take_succ_cons, List.take_zero] at ho
  rw [ho, ho']
  cases s with
  | zero => omega
  | succ s =>
    simp only [List.take_succ_cons, List.append_assoc, List.singleton_append]
    intro hc
    exact (List.isChain_append_cons_cons.mp hc).2.1 rfl

/-- 概要：前半の直後の文字で抽出を終える行長を同定する（BF §1.5.8）。
方針：可用行の非重複性から、同じ文字を指す二つの添字を一致させる。
規約：r は正。末尾文字は可用行の r−1 番目として指定する。
使われ方：行長を仮定せず、実際の抽出末尾から境界重複を検出する。 -/
lemma available_endpoint_prefix_length (pre post removed : List α) (a : α)
    (hn : (pre ++ a :: post).Nodup) (r : ℕ) (hr : 0 < r)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post))[r - 1]? = some a) :
    r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre).length + 1 := by
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp he
  have har : a ∉ removed := by
    have hm := List.getElem_mem hi
    rw [hv] at hm
    exact (List.mem_filter.mp hm).2 |> of_decide_eq_true
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre ++ a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed post := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, List.filter_cons,
      decide_eq_true har, ite_true]
  have hj : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre).length <
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post)).length := by
    rw [hs]
    simp only [List.length_append, List.length_cons]
    omega
  have hv' : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post))[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed pre).length] =
      a := by simp [hs]
  have heq := (hn.filter (fun x => decide (x ∉ removed))).getElem_inj_iff.mp
    (hv.trans hv'.symm)
  omega

/-- 概要：実際の末尾文字から前半集合の一致による境界退化を導く（BF §1.5.8）。
方針：成功から正の行長を取り出し、非重複な行で末尾の位置を一意に決める。
規約：前行だけに非重複性を要求する。
使われ方：垂直成分の任意の外側末尾を排除する。 -/
lemma reduceRows_reordered_endpoint_not_isChain (pre pre' : List α) (a : α)
    (post post' : List α) (hm : ∀ x, x ∈ pre' ↔ x ∈ pre)
    (hn : (pre ++ a :: post).Nodup) (removed out : List α)
    (r s : ℕ) (rest : List (List α × ℕ))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: post))[r - 1]? = some a)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((pre ++ a :: post, r) :: (pre' ++ a :: post', s) :: rest)
      removed = some out) : ¬ out.IsChain (· ≠ ·) := by
  have hr := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h).1
  have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_endpoint_prefix_length pre post removed a hn r hr he
  have ha : a ∉ pre := by
    intro ha
    exact (List.nodup_append.mp hn).2.2 a ha a (by simp) rfl
  have har : a ∉ removed := by
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp he
    have hm := List.getElem_mem hi
    rw [hv] at hm
    exact (List.mem_filter.mp hm).2 |> of_decide_eq_true
  subst r
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_reordered_prefix_not_isChain pre pre' a post post' hm ha
    removed out har s rest h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
