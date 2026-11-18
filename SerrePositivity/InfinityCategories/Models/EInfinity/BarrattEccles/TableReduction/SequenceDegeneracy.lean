module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListDegeneracy

/-!
模型。文献の定義との比較は後で
# 退化な置換列に対する table reduction の消滅

概要：Berger–Fresse §1.4.1 の正規化への降下を一般の置換列で証明する。
方針：同じ隣接頂点を table の同じ隣接行へ移し、各項の出力を退化とする。
規約：頂点の位置は有限添字の自然数値の差が 1 であることによって指定する。
使われ方：TR の微分保存で退化項を取り除き、正規化鎖の計算と照合する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：置換の一行表示には重複がない（BF §1.4.1）。
方針：リストの添字による評価の単射性を置換の単射性から得る。
規約：逆置換の一行表示を使う。
使われ方：同じ隣接行の退化補題の入力となる。 -/
lemma permutation_row_nodup {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (List.ofFn (fun j => σ⁻¹ j)).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j h
  simp only [List.getElem_ofFn] at h
  apply Fin.ext
  exact congrArg (fun k : Fin n => k.val) (σ.symm.injective h)

/-- 概要：隣接する二要素の位置でリストを分割する（BF §1.4.1）。
方針：take と drop の分割で次の二文字を展開する。
規約：両方の位置が範囲内にある。
使われ方：同じ隣接行を任意の先行行から切り出す。 -/
lemma list_eq_take_two_drop {α : Type*} (xs : List α) (k : ℕ) (hk : k + 1 < xs.length) :
    xs = xs.take k ++ xs[k] :: xs[k + 1] :: xs.drop (k + 2) := by
  have hk₀ : k < xs.length := by omega
  conv_lhs => rw [← List.take_append_drop k xs]
  rw [List.drop_eq_getElem_cons hk₀, List.drop_eq_getElem_cons hk]

/-- 概要：table の行の添字評価（BF §1.3.1）。
方針：ofFn を指定した有限添字で読む。
規約：行長と置換の逆の一行表示の組。
使われ方：頂点の等式を実際の行の等式へ移す。 -/
lemma rows_getElem {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin (d + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r)[i.val]'(by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn]; exact i.isLt) =
      (List.ofFn (fun k => (w i)⁻¹ k), (r.val i).val) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.getElem_ofFn, Fin.eta]

/-- 概要：等しい隣接頂点を持つ列の抽出出力は退化（BF §1.4.1）。
方針：該当する二行を分割して同じ隣接行の一般補題を適用する。
規約：全ての行長の選択・成功した出力で成立する。
使われ方：退化列で TR の各項を零にする。 -/
lemma output_not_isChain_of_adjacent_eq {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (i j : Fin (d + 1))
    (hij : i.val + 1 = j.val) (hw : w i = w j) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  have hk : i.val + 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, hij] using j.isLt
  have hsplit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.list_eq_take_two_drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) i.val hk
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_getElem w r i] at hsplit
  have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r)[i.val + 1] =
      (List.ofFn (fun k => (w i)⁻¹ k), (r.val j).val) := by
    simpa only [hij, hw] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_getElem w r j
  rw [he] at hsplit
  rw [hsplit] at h
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_same_adjacent_not_isChain _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.permutation_row_nodup (w i)) _ _ _ _ _ h

variable (A : Type u) [CommRing A]

/-- 概要：退化な置換列の各 table 項は零（BF §1.4.1）。
方針：抽出失敗なら零、成功なら隣接重複による正規化の消滅を使う。
規約：基礎環の標数は任意。
使われ方：TR の有限和全体の消滅を導く。 -/
lemma term_eq_zero_of_adjacent_eq {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (i j : Fin (d + 1))
    (hij : i.val + 1 = j.val) (hw : w i = w j) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term
  cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] with
  | none => rfl
  | some out =>
    simp only [Option.map_some, Option.getD_some]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_eq_zero_of_not_isChain A out
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_not_isChain_of_adjacent_eq w i j hij hw r out h)

/-- 概要：等しい隣接頂点を持つ任意の列で TR は零（BF §1.4.1）。
方針：各 table 項の零を有限和へ移し、nullary 分岐を照合する。
規約：全 arity・全次数を含む。
使われ方：TR の正規化への降下と微分保存での退化項の除去に使う。 -/
lemma onSequence_eq_zero_of_adjacent_eq {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (i j : Fin (d + 1))
    (hij : i.val + 1 = j.val) (hw : w i = w j) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = 0 := by
  have hd : d ≠ 0 := by intro hd; subst d; have := j.isLt; omega
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence
  split
  · simp
  · apply Finset.sum_eq_zero
    intro r _
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term_eq_zero_of_adjacent_eq A w i j hij hw r

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
