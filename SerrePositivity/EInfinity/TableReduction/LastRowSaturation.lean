module

public import SerrePositivity.EInfinity.TableReduction.PrefixExclusions
public import SerrePositivity.EInfinity.TableReduction.AvailableCardinality

/-!
# 成功 table の最後の行の利用可能長の飽和

概要：Berger–Fresse §1.4.4 の逆構成で、除外を解いた値が最後まで未選択とはならないことを準備する。
方針：先行行の除外長を n−最終行長と計数し、置換行の利用可能長を求める。
規約：行長の総和と正値性は実際の Schedule の条件を使う。
使われ方：逆対応で影響を受ける最初の行の存在と最終末尾の分岐を保証する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：最終行より前の長さ−1 の和と最終行長の和は arity（BF §1.4.4）。
方針：全行長の総和と先行行数を Schedule から読む。
規約：最後の行の一行表示も実際の行リストで指定する。
使われ方：先行抽出後の除外長を計数する。 -/
lemma before_last_excess {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (before : List (List (Fin n) × ℕ))
    (he : rows w r = before ++ [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)]) :
    (before.map (fun p => p.2 - 1)).sum + (r.val (Fin.last d)).val = n := by
  have hl := congrArg List.length he
  simp only [rows, List.length_ofFn, List.length_append, List.length_singleton] at hl
  have hs := rows_sum w r
  rw [he] at hs
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero] at hs
  have hp : ∀ x ∈ before.map Prod.snd, 0 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hm : p ∈ rows w r := by rw [he]; exact List.mem_append_left _ hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    have hx := congrArg Prod.snd hi
    have hpos := r.property.1 i
    dsimp only at hx
    omega
  have hb := sum_sub_one_add_length (before.map Prod.snd) hp
  simp only [List.map_map, List.length_map] at hb
  change (before.map (fun p => p.2 - 1)).sum + before.length =
    (before.map Prod.snd).sum at hb
  omega

/-- 概要：元の Schedule の最終行は利用可能な全ての値をちょうど選ぶ（BF §1.4.4）。
方針：除外状態の重複のなさと長さ、利用可能長の計数を合わせる。
規約：元の成功抽出の先行証跡を入力とする。
使われ方：解放値が最後の行では必ず延長選択の範囲内にあることを導く。 -/
lemma last_row_available_length {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (before : List (List (Fin n) × ℕ))
    (he : rows w r = before ++ [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)])
    (picked : List (List (Fin n))) (finish : List (Fin n))
    (h : ExtractionPrefix before [] picked finish) :
    (available finish (vertexRow w (Fin.last d))).length = (r.val (Fin.last d)).val := by
  have hn : finish.Nodup := h.finish_nodup (by simp) (by
    intro p hp
    apply rows_nodup w r p
    rw [he]
    exact List.mem_append_left _ hp)
  have hl := h.finish_length
  simp only [List.length_nil, Nat.zero_add] at hl
  have hs := before_last_excess w r before he
  have hc := available_vertexRow_length_add w (Fin.last d) finish hn
  omega

/-- 概要：任意の成功 table の最終行直前の実際の状態と利用可能長（BF §1.4.4）。
方針：最後の行だけを残して先行抽出を分離する。
規約：次数零の一行 table も含む。
使われ方：最後の行まで続いた逆の探索の終端条件を供給する。 -/
lemma final_prefix_saturated {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out) :
    ∃ before picked finish tail,
      rows w r = before ++ [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)] ∧
      ExtractionPrefix before [] picked finish ∧
      reduceRows [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)] finish = some tail ∧
      (available finish (vertexRow w (Fin.last d))).length = (r.val (Fin.last d)).val := by
  have hb : d < (rows w r).length := by simp only [rows, List.length_ofFn]; omega
  have hd : (rows w r).drop (d + 1) = [] := List.drop_eq_nil_iff.mpr (by
    simp only [rows, List.length_ofFn]
    omega)
  have he : rows w r = (rows w r).take d ++
      [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)] := by
    calc
      _ = (rows w r).take d ++ (rows w r).drop d := (List.take_append_drop d _).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons hb, hd]
        simp only [rows, List.getElem_ofFn, vertexRow, Fin.last]
  have hs : reduceRows ((rows w r).take d ++
      [(vertexRow w (Fin.last d), (r.val (Fin.last d)).val)]) [] = some out := by
    rw [← he]; exact h
  obtain ⟨picked, finish, tail, hp, ht, _⟩ := extractionPrefix_of_reduceRows _ _ [] out hs
  exact ⟨(rows w r).take d, picked, finish, tail, he, hp, ht,
    last_row_available_length w r _ he picked finish hp⟩

end SerrePositivity.EInfinity.TableReduction
