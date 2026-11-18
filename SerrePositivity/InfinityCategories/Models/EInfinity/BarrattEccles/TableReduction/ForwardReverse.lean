module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardReverseSearch
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalOccurrenceUnique

/-!
模型。文献の定義との比較は後で
# 順方向の相手からの逆構成は元の削除を復元する

概要：Berger–Fresse §1.4.4 の順から逆の Schedule・成功出力・削除位置の一致を証明する。
方針：探索から二行を同定し、行長移動の逆と最終出現の一意性を適用する。
規約：逆構成の選択に依存せず、退化した相手の出力も扱う。
使われ方：二種類の残余削除の全単射のもう一方の逆関係を与える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：逆構成の二行が元の行なら Schedule は元へ戻る（BF §1.4.4）。
方針：行長移動の逆公式と二行の等式を使う。
規約：長さと不等号の証明項の選択には依存しない。
使われ方：順から逆の実際の抽出の始点を元の Schedule へ戻す。 -/
lemma reverse_schedule_eq {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (donor : Fin (d + 1)) (receiver : Fin d) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (early : Fin d) (late : Fin (d + 1))
    (order : early.castSucc < late)
    (long : 1 < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc
      (ne_of_gt ho) hd).val early.castSucc).val)
    (he : early = receiver) (hl : late = donor) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd)
      early.castSucc late (ne_of_lt order) long = r := by
  subst early late
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_inverse r donor receiver.castSucc (ne_of_gt ho) hd

/-- 概要：順方向の相手に対する任意の逆構成は元の出力と削除位置を返す（BF §1.4.4）。
方針：同じ解放値と二行を探索で復元し、成功出力と最終出現の一意性を使う。
規約：変更後の出力の非退化性は要求しない。
使われ方：残余削除の対応を全単射として束ねるための順から逆の等式。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.reverse_result {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (k : Fin out.length)
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val)
    (hh : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val)
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val)
    (new : List (Fin n))
    (hnew : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc
      (ne_of_gt ho) hd)) [] = some new) (q : Fin new.length)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val)
    (rb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd) new q) :
    rb.new = out ∧ rb.point.val = k.val := by
  obtain ⟨ha, hearly, hlate⟩ := b.reverse_search h ho hd k hl hh hf hp he new hnew q hq rb
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverse_schedule_eq r donor receiver ho hd rb.early rb.late rb.order rb.long
    hearly hlate
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some rb.new := by
    simpa only [hs] using rb.success
  have hout : rb.new = out := Option.some.inj (hsuccess.symm.trans h)
  refine ⟨hout, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_occurrence_unique rb.new out hout rb.point k rb.point_not_caesura hf
  exact rb.point_value_eq.trans ha

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
