module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletedVertexRows

/-!
模型。文献の定義との比較は後で
# 除外長の上界による一文字行の挿入

概要：Berger–Fresse §1.4.4 の頂点削除の逆操作が抽出成功を保つことを示す。
方針：挿入位置までの除外数を行長−1 の和で抑え、残る文字を一つ取る。
規約：挿入行は重複を持たず、その長さは除外数より大きい。
使われ方：頂点境界の成功 table から一文字行を持つ成功 table を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：除外リストより長い重複のない行には利用可能な文字がある（BF §1.4.4）。
方針：全て除外されるなら部分集合の長さの比較に反する。
規約：除外リスト自体は重複していてよい。
使われ方：挿入する一文字行の抽出が失敗しないことを保証する。 -/
lemma available_ne_nil_of_length {α : Type*} [DecidableEq α]
    (removed row : List α) (hn : row.Nodup) (hl : removed.length < row.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row ≠ [] := by
  intro he
  have hs : row ⊆ removed := by
    intro a ha
    by_contra hm
    have hx : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row := by
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, decide_eq_true_eq]
      exact ⟨ha, hm⟩
    rw [he] at hx
    exact List.not_mem_nil hx
  have hb := hn.length_le_of_subset hs
  omega

/-- 概要：除外数の余裕があれば任意の位置に一文字行を挿入できる（BF §1.4.4）。
方針：先行行で帰納し、除外リストの長さに抽出長−1 を加える。
規約：前後の出力と挿入位置を同時に保持する。
使われ方：元の頂点を復元して成功した table を再構成する。 -/
lemma reduceRows_insert_singleton {α : Type*} [DecidableEq α]
    (before : List (List α × ℕ)) (row : List α) (rest : List (List α × ℕ))
    (removed out : List α) (hn : row.Nodup)
    (hb : removed.length + (before.map (fun p => p.2 - 1)).sum < row.length)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) removed = some out) :
    ∃ pre a post, out = pre ++ post ∧ pre.length = (before.map Prod.snd).sum ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, 1) :: rest) removed = some (pre ++ a :: post) := by
  induction before generalizing removed out with
  | nil =>
    have hne : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row ≠ [] := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_ne_nil_of_length _ _ hn (by
      simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using hb)
    cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row with
    | nil => exact False.elim (hne he)
    | cons a xs =>
      refine ⟨[], a, out, rfl, rfl, ?_⟩
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row 1 rest removed out (by omega)
        (by rw [he]; simp) (by simpa using h)
      simpa only [he, List.take_succ_cons, List.take_zero, List.singleton_append,
        List.nil_append] using hs
  | cons p before ih =>
    obtain ⟨hr, hlen, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    have hbudget : (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take (p.2 - 1)).length +
        (before.map (fun p => p.2 - 1)).sum < row.length := by
      have hle : p.2 - 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).length := by omega
      simp only [List.length_append, List.length_take, Nat.min_eq_left hle]
      simp only [List.map_cons, List.sum_cons] at hb
      omega
    obtain ⟨pre, a, post, hp, hl, hc⟩ := ih _ _ hbudget ht
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 ++ pre, a, post, ?_, ?_, ?_⟩
    · rw [he, hp, List.append_assoc]
    · simp only [List.length_append, List.length_take, Nat.min_eq_left hlen, hl,
        List.map_cons, List.sum_cons]
    · have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success p.1 p.2 (before ++ (row, 1) :: rest)
        removed (pre ++ a :: post) hr hlen hc
      simpa only [List.cons_append, List.append_assoc] using hs

/-- 概要：正の行長では行長−1 の総和は総長−行数（BF §1.4.4）。
方針：一行ずつ 1 を足し戻す。
規約：自然数の減算を使い、各行長の正値性を要求する。
使われ方：Schedule 全体の除外数の余裕を n−1 と評価する。 -/
lemma sum_sub_one_add_length (xs : List ℕ) (hn : ∀ x ∈ xs, 0 < x) :
    (xs.map (fun x => x - 1)).sum + xs.length = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hn x (by simp)
    have ht := ih (fun y hy => hn y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- 概要：Schedule の任意の先行部分の除外予算は arity 未満（BF §1.4.4）。
方針：全体の予算と残りの非負の予算を比較する。
規約：先頭から k 行を取り、最後まで取ってもよい。
使われ方：末尾を含むどの位置でも一文字行を挿入できる。 -/
lemma rows_prefix_budget {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (k : ℕ) :
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take k).map (fun p => p.2 - 1)).sum < n := by
  have hp : ∀ x ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd, 0 < x := by
    intro x hx
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact r.property.1 i
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_sub_one_add_length ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd) hp
  have hl : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd).length = d + 1 := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows]
  rw [hl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_sum w r] at hsum
  have ht := List.sum_take_add_sum_drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map (fun p => p.2 - 1)) k
  have he : (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd).map (fun x => x - 1)).sum =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map (fun p => p.2 - 1)).sum := by rw [List.map_map]; rfl
  rw [he] at hsum
  rw [← List.map_take] at ht
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
