module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOutputUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SequenceDegeneracy
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace

/-!
模型。文献の定義との比較は後で
# 同じ成功出力の行分割の一意性と任意の行からの再開

概要：Berger–Fresse §1.5.8–9 の経路復元で、二つの成功表の全選択行を揃える。
方針：リスト出力を有限語へ移して Schedule を一致させ、平坦化と全行長で選択行を一致させる。
規約：置換列は異なってよい。非退化性は一意性には不要。
使われ方：同じ出力の行境界を比較して shuffle の水平・垂直辺を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：同じリスト出力を持つ成功 Schedule は等しい（BF §1.5.8–9）。
方針：成功出力の長さから有限語を作り、既存の Schedule 一意性を適用する。
規約：左右の置換列は異なってよい。
使われ方：実際の経路成功と復元経路成功の行長を揃える。 -/
lemma schedule_eq_of_same_list {n d : ℕ}
    (w w' : Fin (d + 1) → Equiv.Perm (Fin n)) (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w' r') [] = some out) :
    r = r' := by
  have hlen : out.length = n + d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h
  let v : Fin (n + d) → Fin n := fun i => out[i.val]'(by rw [hlen]; exact i.isLt)
  have hv : List.ofFn v = out := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← hv] at h h'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output w w' r r' v h h'

/-- 概要：同じ成功出力の二つの実際の選択行列は等しい（BF §1.5.8–9）。
方針：Schedule 一意性で全行長を揃え、平坦化と行長の一致から行列を一致させる。
規約：元の置換列も Schedule も左右で異なってよい。
使われ方：出力だけから決まる同じ境界文字を二つの経路で比較する。 -/
lemma selected_eq_of_same_output {n d : ℕ}
    (w w' : Fin (d + 1) → Equiv.Perm (Fin n)) (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    {picked picked' : List (List (Fin n))}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked) (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w' r') [] picked')
    (hout : picked.flatten = picked'.flatten) : picked = picked' := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_list w w' r r' picked.flatten h.reduceRows
    (by rw [hout]; exact h'.reduceRows)
  subst r'
  apply List.eq_iff_flatten_eq.mpr
  refine ⟨hout, ?_⟩
  have hl := h.lengths
  have hl' := h'.lengths
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def] at hl hl'
  exact hl.trans hl'.symm

variable {α : Type*} [DecidableEq α]

/-- 概要：抽出証跡を任意の行から再開できる（BF §1.5.8）。
方針：捨てる行数で帰納し、実際の更新後の除外状態を次へ渡す。
規約：全行を越えて進む場合も空の証跡を返す。
使われ方：指定辺の前後の実際の隣接行を取り出す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.drop {rows : List (List α × ℕ)} {removed : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) (i : ℕ) :
    ∃ middle, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (rows.drop i) middle (picked.drop i) := by
  induction i generalizing rows removed picked with
  | zero => exact ⟨removed, h⟩
  | succ i ih =>
    cases h with
    | nil => exact ⟨removed, .nil _⟩
    | cons hr hb ht => exact ih ht

omit [DecidableEq α] in
/-- 概要：全選択語の非退化性は任意の後続行列へ制限できる（BF §1.5.8）。
方針：行列を take と drop の連結へ分け、語の連結の後半を取る。
規約：除外状態や行長には依存しない。
使われ方：指定辺から後の成功へ元の非退化性を渡す。 -/
lemma flatten_drop_isChain (picked : List (List α)) (i : ℕ)
    (hc : picked.flatten.IsChain (· ≠ ·)) : (picked.drop i).flatten.IsChain (· ≠ ·) := by
  have he : picked.flatten = (picked.take i).flatten ++ (picked.drop i).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [he] at hc
  exact hc.right_of_append

/-- 概要：実際の Schedule の指定辺から二行を明示して行列を再開する（BF §1.5.8）。
方針：drop の先頭二要素を有限列の二つの頂点と行長で評価する。
規約：辺 i の二頂点は i.castSucc と i.succ。
使われ方：格子経路の辺条件を実際の隣接二行の成功へ適用する。 -/
lemma rows_drop_two {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i : Fin d) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop i.val =
      (List.ofFn (w i.castSucc).symm, (r.val i.castSucc).val) ::
        (List.ofFn (w i.succ).symm, (r.val i.succ).val) :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2) := by
  have hi : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn]; omega
  have hj : i.val + 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn]; omega
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.getElem_ofFn]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
