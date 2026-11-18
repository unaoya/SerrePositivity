module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowOwners
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PreviousOccurrenceRow
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferBounds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonPositions

/-!
模型。文献の定義との比較は後で
# 残余の最終出現削除で移す二つの行

概要：Berger–Fresse §1.4.4 の相殺の行長移動に使う削除行と受け取り行を取り出す。
方針：削除位置の所属行と直前の出現の行末を比較し、一文字行の除外を使う。
規約：退化出力も扱い、残余和に残る削除位置だけを対象にする。
使われ方：実際の Schedule の移動の入力と最終出現の削除符号を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：残余位置の所属行は長さ 2 以上（BF §1.4.4）。
方針：長さ 1 なら行内添字は零で、削除位置は一文字行の開始位置に属する。
規約：出力の成功と行内位置の分解を保持する。
使われ方：相殺相手の Schedule の減らす行の正値性を与える。 -/
lemma owner_length_gt_one_of_remaining {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out pre row : List (Fin n)) (hl : out.length = n + d)
    (i : Fin (d + 1)) (j : Fin row.length) (k : Fin out.length)
    (hp : pre.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i) (hr : row.length = (r.val i).val)
    (hk : k.val = pre.length + j.val) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out hl) :
    1 < (r.val i).val := by
  have hpos := r.property.1 i
  by_contra hb
  have hi : (r.val i).val = 1 := by omega
  have hj : j.val = 0 := by have := j.isLt; omega
  apply hx
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
  apply Fin.ext
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i = k.val
  omega

/-- 概要：残余の最終出現削除には先行する受け取り行と長さ 2 以上の削除行がある（BF §1.4.4）。
方針：同じ行内の重複を排除して、直前の出現の行末が削除行より前にあると示す。
規約：直前の出現があることを要求し、退化出力も含む。
使われ方：長さの移動の二行・順序・余裕と削除係数を同時に指定する。 -/
lemma final_deletion_location {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d),
      receiver.castSucc < donor ∧ 1 < (r.val donor).val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val ∧ k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val ∧
      (r.val receiver.castSucc).val < n ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
        -((-1 : ℤ) ^ receiver.val) := by
  obtain ⟨donor, pre, row, post, j, he, hn, hstart, hlength, hk⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_position_owner w r out h k
  obtain ⟨receiver, hreceive, hcoeff⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_coefficient_receiver w r out h k hf hp
  let p := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp
  have hm := Finset.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k) hp
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hbefore : p.val < pre.length :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.previous_position_before_owner out pre row post he hn k p j hk hm.1 hm.2
  have horder : receiver.castSucc < donor := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.row_lt_of_end_lt_start r receiver donor (by omega)
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.owner_length_gt_one_of_remaining r out pre row (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h)
    donor j k hstart hlength hk hx
  have hne : donor ≠ receiver.castSucc := ne_of_gt horder
  have hj := j.isLt
  refine ⟨donor, receiver, horder, hd, ?_, ?_,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_receiver_lt r donor receiver.castSucc hne hd, hreceive, hcoeff⟩
  · omega
  · omega

/-- 概要：残余の最終出現削除で移す二行と余裕・符号（BF §1.4.4）。
方針：所属位置も保持する強い証明書から行長と符号の部分を取り出す。
規約：既存の二行の指定の公開界面を保つ。
使われ方：行長変更の構成と係数比較へ必要な部分だけを渡す。 -/
lemma final_deletion_rows {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d),
      receiver.castSucc < donor ∧ 1 < (r.val donor).val ∧ (r.val receiver.castSucc).val < n ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
        -((-1 : ℤ) ^ receiver.val) := by
  obtain ⟨donor, receiver, ho, hd, _, _, hr, he, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_location w r out h k hx hf hp
  exact ⟨donor, receiver, ho, hd, hr, he, hc⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
