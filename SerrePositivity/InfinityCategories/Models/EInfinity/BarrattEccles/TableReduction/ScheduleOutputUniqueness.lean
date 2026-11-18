module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleLineRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ResidualRowEnds

/-!
模型。文献の定義との比較は後で
# 成功出力だけで決まる行長 Schedule の一意性

概要：Berger–Fresse §1.5.8–9 の逆構成で元の成功表の行長が出力語だけから決まることを示す。
方針：出力の各位置の lineRank から全行の開始位置を同定し、隣接開始位置の差を取る。
規約：置換列は左右で異なってよく、出力の非退化性も要求しない。
使われ方：語と分割の復元を元の成功 Schedule の一意性へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：同じ成功出力の他方の同じ行の開始は元の開始以前（BF §1.5.8–9）。
方針：元の行の先頭の lineRank を他方の元の所属行へ戻す。
規約：元の置換列は同じでなくてもよい。
使われ方：両向きに適用して全行の開始位置を同定する。 -/
lemma scheduleOffset_le_of_same_output {n d : ℕ}
    (w w' : Fin (d + 1) → Equiv.Perm (Fin n)) (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w' r') [] = some (List.ofFn v)) (i : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' i ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i := by
  let p : Fin (n + d) := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_lt r i⟩
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_schedule_of_reduction w r v h i 0 (r.property.1 i)
  simp only [Nat.add_zero] at hr
  obtain ⟨j, hj, hlo, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_owner_of_reduction w' r' v h' p
  have he : j = i := Fin.ext (hj.symm.trans hr)
  subst j
  exact hlo

/-- 概要：同じ成功出力を与える二つの行長 Schedule は等しい（BF §1.5.8–9）。
方針：全開始位置の一致で非最終行長を揃え、総長で最終行長を揃える。
規約：置換列の一致・出力の全射性や非退化性を仮定しない。
使われ方：逆構成と全合成項対応の元の Schedule の一意性。 -/
lemma schedule_eq_of_same_output {n d : ℕ}
    (w w' : Fin (d + 1) → Equiv.Perm (Fin n)) (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w' r') [] = some (List.ofFn v)) : r = r' := by
  have hoff (i : Fin (d + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r' i :=
    Nat.le_antisymm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_le_of_same_output w' w r' r v h' h i)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_le_of_same_output w w' r r' v h h' i)
  have hf (i : Fin d) : (r.val i.castSucc).val = (r'.val i.castSucc).val := by
    have h1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_succ r i
    have h2 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_succ r' i
    rw [hoff i.succ, hoff i.castSucc] at h1
    omega
  apply Subtype.ext
  funext i
  apply Fin.ext
  cases i using Fin.lastCases with
  | cast i => exact hf i
  | last =>
    have h1 := r.property.2
    have h2 := r'.property.2
    rw [Fin.sum_univ_castSucc] at h1 h2
    have hs : (∑ i : Fin d, (r.val i.castSucc).val) =
        ∑ i : Fin d, (r'.val i.castSucc).val := Finset.sum_congr rfl (fun i _ => hf i)
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
