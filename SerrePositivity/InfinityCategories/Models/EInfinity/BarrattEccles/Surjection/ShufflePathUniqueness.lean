module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleBoundaryRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionPathSuccess

/-!
模型。文献の定義との比較は後で
# 非退化な成功出力だけで決まる shuffle 経路

概要：Berger–Fresse §1.5.8–9 の逆構成で、同じ非退化出力を与える全経路を一致させる。
方針：Schedule と選択行列を一致させ、各辺の垂直性を同じ境界文字から判定する。
規約：両経路の元の置換列は異なってよい。
使われ方：元の成功から復元した compositionPath と fusedSchedule の往復を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：同じ非退化成功出力を持つ二つの shuffle 経路は等しい（BF §1.5.8–9）。
方針：出力による選択行列の一意性と全境界の内側性で水平辺集合を一致させる。
規約：元の置換列と Schedule は左右で異なってよく、出力の全射性は仮定しない。
使われ方：元の成功項の実際の経路を逆構成の経路へ戻す。 -/
lemma shufflePath_eq_of_same_output {m n d e : ℕ} (k : Fin (m + 1)) (s t : ShufflePath d e)
    (outer outer' : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner inner' : Fin (e + 1) → Equiv.Perm (Fin n)) (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (s.horizontal j))
      (inner (s.vertical j))) r) [] = some out)
    (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer' (t.horizontal j))
      (inner' (t.vertical j))) r') [] = some out) (hc : out.IsChain (· ≠ ·)) : s = t := by
  obtain ⟨picked, ht, hf⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ [] out h
  obtain ⟨picked', ht', hf'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ [] out h'
  have hp : picked = picked' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.selected_eq_of_same_output _ _ r r' ht ht' (hf.trans hf'.symm)
  subst picked'
  have hchain : picked.flatten.IsChain (· ≠ ·) := by rw [hf]; exact hc
  apply Subtype.ext
  apply Finset.ext
  intro i
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.boundaryInserted_iff_notMem k s outer inner r picked ht hchain i
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.boundaryInserted_iff_notMem k t outer' inner' r' picked ht' hchain i
  by_cases hm : i ∈ s.val
  · have hm' : i ∈ t.val := by
      by_contra hn
      exact (hs.mp (ht.mpr hn)) hm
    exact iff_of_true hm hm'
  · have hm' : i ∉ t.val := ht.mp (hs.mpr hm)
    exact iff_of_false hm hm'

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：構成した compositionPath は同じ出力を与える元の経路と一致（BF §1.5.8–9）。
方針：正方向の実際の成功と元の成功に経路一意性を適用する。
規約：構成した経路との一致を入力に要求しない。
使われ方：一般の合成項対応の逆方向と正方向の往復。 -/
lemma compositionPath_eq_of_success {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (s : ShufflePath d e) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n c.slot (c.outer (s.horizontal j))
      (c.inner (s.vertical j))) r) [] = some out) (hc : out.IsChain (· ≠ ·))
    (hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts = out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts = s := by
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule) [] = some out := by
    rw [← hw]
    exact c.pathSequence_success
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shufflePath_eq_of_same_output c.slot _ s c.outer c.outer c.inner c.inner
    c.fusedSchedule r out hs h hc

/-- 概要：構成した fusedSchedule は同じ出力を与える元の Schedule と一致（BF §1.5.8–9）。
方針：二つの実際の成功の出力一致を既存の Schedule 一意性へ渡す。
規約：経路一致や非退化性をこの Schedule 一意性には要求しない。
使われ方：元の経路と Schedule をともに復元して全成功項の対応を構成する。 -/
lemma fusedSchedule_eq_of_success {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (s : ShufflePath d e) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) (out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n c.slot (c.outer (s.horizontal j))
      (c.inner (s.vertical j))) r) [] = some out)
    (hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts = out) : c.fusedSchedule = r := by
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule) [] = some out := by
    rw [← hw]
    exact c.pathSequence_success
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_list c.pathSequence _ c.fusedSchedule r out hs h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
