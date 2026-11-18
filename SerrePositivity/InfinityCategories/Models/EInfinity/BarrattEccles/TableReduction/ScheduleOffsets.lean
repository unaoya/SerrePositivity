module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonBoundary

/-!
模型。文献の定義との比較は後で
# Schedule の行開始位置の単調性

概要：Berger–Fresse §1.4.4 の一文字行の削除位置を重複なく指定する。
方針：正の行長の部分和を取り、隣接部分和が必ず増えることを示す。
規約：開始位置は零始まり、最後の行も含む。
使われ方：全ての削除位置を一文字行の位置と残りに分ける。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：自然数リストの部分和は添字について単調（BF §1.4.4）。
方針：長い先行部分をさらに take と drop に分ける。
規約：添字がリスト長を超える場合も許す。
使われ方：行長の部分和の狭義単調性を導く。 -/
lemma sum_take_mono (xs : List ℕ) {i j : ℕ} (hij : i ≤ j) :
    (xs.take i).sum ≤ (xs.take j).sum := by
  have hs := List.sum_take_add_sum_drop (xs.take j) i
  rw [List.take_take, Nat.min_eq_left hij] at hs
  omega

/-- 概要：正の成分を一つ含めると部分和は狭義に増える（BF §1.4.4）。
方針：take(i+1) の末尾を分けて正の値を加える。
規約：i はリストの範囲内、j はそれより大きい。
使われ方：異なる行が同じ削除位置を指定しないことを保証する。 -/
lemma sum_take_strictMono (xs : List ℕ) (hn : ∀ x ∈ xs, 0 < x)
    {i j : ℕ} (hi : i < xs.length) (hij : i < j) :
    (xs.take i).sum < (xs.take j).sum := by
  have hp : 0 < xs[i] := hn _ (List.getElem_mem hi)
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_take_mono xs (by omega : i + 1 ≤ j)
  rw [List.take_succ_eq_append_getElem hi, List.sum_append] at hb
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hb
  omega

/-- 概要：Schedule の指定行より前の全行長（BF §1.4.4）。
方針：行長のリストの先行部分を加える。
規約：第零行の開始位置は零。
使われ方：一文字行の削除する文字の位置を指定する。 -/
def scheduleOffset {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin (d + 1)) : ℕ :=
  ((List.ofFn (fun j => (r.val j).val)).take i.val).sum

/-- 概要：Schedule の開始位置は行番号について狭義単調（BF §1.4.4）。
方針：全ての行長が正であることを部分和の一般補題へ渡す。
規約：全ての arity と次数に対して、Schedule があれば成立する。
使われ方：一文字行の削除位置の添字の単射性を与える。 -/
lemma scheduleOffset_strictMono {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r) := by
  intro i j hij
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_take_strictMono
  · intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact r.property.1 k
  · simpa only [List.length_ofFn] using i.isLt
  · exact hij

/-- 概要：行の開始位置は出力の全長より前（BF §1.4.4）。
方針：次の正の行長を含む部分和と全体の和を比較する。
規約：最終行の開始位置も含む。
使われ方：開始位置を実際の出力の有限添字として使う。 -/
lemma scheduleOffset_lt {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i < n + d := by
  have hp : ∀ x ∈ List.ofFn (fun j => (r.val j).val), 0 < x := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact r.property.1 k
  have hi : i.val < (List.ofFn (fun j => (r.val j).val)).length := by
    simpa only [List.length_ofFn] using i.isLt
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_take_strictMono (List.ofFn (fun j => (r.val j).val)) hp hi hi
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset, List.take_length, List.sum_ofFn, r.property.2] using hs

/-- 概要：行の開始位置を実際の出力リストの添字へ移す（BF §1.4.4）。
方針：出力長の等式と開始位置の上界を合わせる。
規約：出力リストの値には依存せず長さだけを使う。
使われ方：一文字行の削除項を出力位置の有限集合として指定する。 -/
def outputPosition {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (hl : out.length = n + d) (i : Fin (d + 1)) : Fin out.length :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i, by rw [hl]; exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_lt r i⟩

/-- 概要：異なる行は出力の異なる開始位置を持つ（BF §1.4.4）。
方針：開始位置の狭義単調性の単射性を適用する。
規約：長さの証明項には依存しない。
使われ方：一文字行から削除位置への有限集合の像に重複がないことを示す。 -/
lemma outputPosition_injective {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (hl : out.length = n + d) : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.outputPosition r out hl) := by
  intro i j hij
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_strictMono r).injective (congrArg Fin.val hij)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
