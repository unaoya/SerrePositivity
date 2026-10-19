module

public import SerrePositivity.EInfinity.TableReduction.RowOwners
public import SerrePositivity.EInfinity.TableReduction.PreviousOccurrenceRow
public import SerrePositivity.EInfinity.TableReduction.TransferBounds
public import SerrePositivity.EInfinity.TableReduction.SingletonPositions

/-!
# 残余の最終出現削除で移す二つの行

概要：Berger–Fresse §1.4.4 の相殺の行長移動に使う削除行と受け取り行を取り出す。
方針：削除位置の所属行と直前の出現の行末を比較し、一文字行の除外を使う。
規約：退化出力も扱い、残余和に残る削除位置だけを対象にする。
使われ方：実際の Schedule の移動の入力と最終出現の削除符号を供給する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：残余位置の所属行は長さ 2 以上（BF §1.4.4）。
方針：長さ 1 なら行内添字は零で、削除位置は一文字行の開始位置に属する。
規約：出力の成功と行内位置の分解を保持する。
使われ方：相殺相手の Schedule の減らす行の正値性を与える。 -/
lemma owner_length_gt_one_of_remaining {n d : ℕ} (r : Schedule n d)
    (out pre row : List (Fin n)) (hl : out.length = n + d)
    (i : Fin (d + 1)) (j : Fin row.length) (k : Fin out.length)
    (hp : pre.length = scheduleOffset r i) (hr : row.length = (r.val i).val)
    (hk : k.val = pre.length + j.val) (hx : k ∉ singletonPositions r out hl) :
    1 < (r.val i).val := by
  have hpos := r.property.1 i
  by_contra hb
  have hi : (r.val i).val = 1 := by omega
  have hj : j.val = 0 := by have := j.isLt; omega
  apply hx
  unfold singletonPositions
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
  apply Fin.ext
  change scheduleOffset r i = k.val
  omega

/-- 概要：残余の最終出現削除には先行する受け取り行と長さ 2 以上の削除行がある（BF §1.4.4）。
方針：同じ行内の重複を排除して、直前の出現の行末が削除行より前にあると示す。
規約：直前の出現があることを要求し、退化出力も含む。
使われ方：長さの移動の二行・順序・余裕と削除係数を同時に指定する。 -/
lemma final_deletion_location {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ singletonPositions r out (output_length w r out h))
    (hf : ¬ Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d),
      receiver.castSucc < donor ∧ 1 < (r.val donor).val ∧
      scheduleOffset r donor ≤ k.val ∧ k.val < scheduleOffset r donor + (r.val donor).val ∧
      (r.val receiver.castSucc).val < n ∧
      scheduleEnd r receiver =
        ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
        -((-1 : ℤ) ^ receiver.val) := by
  obtain ⟨donor, pre, row, post, j, he, hn, hstart, hlength, hk⟩ :=
    output_position_owner w r out h k
  obtain ⟨receiver, hreceive, hcoeff⟩ := final_deletion_coefficient_receiver w r out h k hf hp
  let p := (previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp
  have hm := Finset.max'_mem (previousOccurrences (fun j : Fin out.length => out[j.val]) k) hp
  simp only [previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hbefore : p.val < pre.length :=
    previous_position_before_owner out pre row post he hn k p j hk hm.1 hm.2
  have horder : receiver.castSucc < donor := row_lt_of_end_lt_start r receiver donor (by omega)
  have hd := owner_length_gt_one_of_remaining r out pre row (output_length w r out h)
    donor j k hstart hlength hk hx
  have hne : donor ≠ receiver.castSucc := ne_of_gt horder
  have hj := j.isLt
  refine ⟨donor, receiver, horder, hd, ?_, ?_,
    schedule_receiver_lt r donor receiver.castSucc hne hd, hreceive, hcoeff⟩
  · omega
  · omega

/-- 概要：残余の最終出現削除で移す二行と余裕・符号（BF §1.4.4）。
方針：所属位置も保持する強い証明書から行長と符号の部分を取り出す。
規約：既存の二行の指定の公開界面を保つ。
使われ方：行長変更の構成と係数比較へ必要な部分だけを渡す。 -/
lemma final_deletion_rows {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ singletonPositions r out (output_length w r out h))
    (hf : ¬ Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d),
      receiver.castSucc < donor ∧ 1 < (r.val donor).val ∧ (r.val receiver.castSucc).val < n ∧
      scheduleEnd r receiver =
        ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
        -((-1 : ℤ) ^ receiver.val) := by
  obtain ⟨donor, receiver, ho, hd, _, _, hr, he, hc⟩ := final_deletion_location w r out h k hx hf hp
  exact ⟨donor, receiver, ho, hd, hr, he, hc⟩

end SerrePositivity.EInfinity.TableReduction
