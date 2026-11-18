module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionRows

/-!
模型。文献の定義との比較は後で
# 最終出現削除の行内部と最終末尾の分岐

概要：Berger–Fresse §1.4.4 の削除行を通過後に合流する場合と、後続が空の場合を分ける。
方針：非最終行の末尾は区切りなので最終出現ではないことを使う。
規約：退化出力も含む。
使われ方：一般の削除位置を通常と末尾の二つのブロック比較へ渡す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：非最終行末に 1 を足すと開始位置＋行長（BF §1.4.4）。
方針：部分和を最後の一成分で分割し、行長の正値性を使う。
規約：行末は零始まりで数える。
使われ方：所属行の末尾かどうかを Schedule の行長で判定する。 -/
lemma scheduleEnd_add_one {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc + (r.val i.castSucc).val := by
  have hb : i.val < (List.ofFn (fun j => (r.val j).val)).length := by
    simp only [List.length_ofFn]; omega
  have he : (List.ofFn (fun j => (r.val j).val))[i.val] = (r.val i.castSucc).val := by
    rw [List.getElem_ofFn]
    exact congrArg (fun j => (r.val j).val) (Fin.ext rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_eq_prefix, List.take_succ_eq_append_getElem hb, List.sum_append, he]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  change _ = ((List.ofFn (fun j => (r.val j).val)).take i.val).sum + _
  have hp := r.property.1 i.castSucc
  omega

/-- 概要：非最終行の末尾は実際の出力でも区切り（BF §1.4.4）。
方針：行末のリストの同定から有限語の再出現条件へ戻す。
規約：行末位置は出力の有限添字として与える。
使われ方：最終出現削除が非最終行の末尾ではないことを保証する。 -/
lemma caesura_of_scheduleEnd {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (i : Fin d) (k : Fin out.length) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k := by
  obtain ⟨picked, he, hn, hl, hlengths, hrep⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r out h
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_eq_scheduleEnds r picked hn hl hlengths i
  rw [hk] at ht
  obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp ht
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_caesura_iff picked out hrep k).mpr
  exact List.mem_iff_getElem.mpr ⟨i.val, hb, hv⟩

/-- 概要：所属行末の最終出現削除は最後の行に限る（BF §1.4.4）。
方針：前の行なら行末が区切りになることに矛盾する。
規約：語の非退化性は不要。
使われ方：末尾の削除行の後続が空であることを導く。 -/
lemma final_deletion_row_end_last {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (donor : Fin (d + 1)) (k : Fin out.length)
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hk : k.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val) : donor.val = d := by
  by_contra hn
  have hd : donor.val < d := by have := donor.isLt; omega
  let i : Fin d := ⟨donor.val, hd⟩
  have hi : i.castSucc = donor := Fin.ext rfl
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r i
  rw [hi] at he
  have hpos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val := by omega
  exact hf (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesura_of_scheduleEnd w r out h i k hpos)

/-- 概要：最終出現削除は行内部か最後の行の末尾（BF §1.4.4）。
方針：所属行の上界で等号か真の不等号に分け、行末の分岐を処理する。
規約：範囲条件は削除位置の所属証明書から得る。
使われ方：通常の donor step と terminal donor step の全ケースを覆う。 -/
lemma final_deletion_row_cases {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (donor : Fin (d + 1)) (k : Fin out.length)
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hk : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val) :
    k.val + 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val ∨
      (donor.val = d ∧ k.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val) := by
  by_cases hi : k.val + 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val
  · exact Or.inl hi
  · have he : k.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val := by omega
    exact Or.inr ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_row_end_last w r out h donor k hf he, he⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
