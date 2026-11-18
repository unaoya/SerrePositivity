module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOffsets
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListDeletionTerms

/-!
模型。文献の定義との比較は後で
# 出力の削除位置の一文字行部分

概要：Berger–Fresse §1.4.4 の一文字行の削除位置を有限集合として取り出す。
方針：一文字行の行番号から開始位置への単射の像を取る。
規約：出力の退化を仮定しない。
使われ方：実際の微分の位置の和を頂点境界と残りの相殺項に分ける。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一文字行に対応する出力の削除位置の集合（BF §1.4.4）。
方針：行長が 1 の行の開始位置を集める。
規約：最後の一文字行も含む。
使われ方：微分の有限和を一文字行の寄与と補集合に分割する。 -/
def singletonPositions {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (hl : out.length = n + d) : Finset (Fin out.length) :=
  (Finset.univ.filter (fun i => (r.val i).val = 1)).image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.outputPosition r out hl)

/-- 概要：一文字行の開始位置の削除項は対応する頂点境界項（BF §1.4.4）。
方針：存在形の削除位置が開始位置と同じ自然数値であることを使う。
規約：位置は出力長の証明書で有限添字に直す。
使われ方：有限集合の像での和の各項を同定する。 -/
lemma listDeletionTerm_singleton (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (i : Fin (d + 2)) (hi : (r.val i).val = 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.outputPosition r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h) i) =
      (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi) := by
  obtain ⟨k, hk, ht⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singleton_deletion_term A w r i hi out h
  have he : k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.outputPosition r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h) i := Fin.ext hk
  subst k
  exact ht

/-- 概要：一文字行の削除位置の和は行番号の有限和（BF §1.4.4）。
方針：開始位置の単射性を使って像の有限和を付け替える。
規約：成功した table の全ての出力を含む。
使われ方：出力位置の和を Schedule の削除・挿入の全単射へ接続する。 -/
lemma sum_singletonPositions (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    (∑ k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) out k) =
      ∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
      else 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions
  rw [Finset.sum_image (fun i _ j _ hij => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.outputPosition_injective r out _ hij)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (r.val i).val = 1
  · simp only [hi, ite_eq_left, dite_eq_left]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.listDeletionTerm_singleton A w r out h i hi
  · simp [hi]

/-- 概要：実際の削除微分は一文字行の寄与と補集合に分かれる（BF §1.4.4）。
方針：出力位置の全体の有限和を指定集合とその補集合へ分ける。
規約：退化項も分割前に捨てない。
使われ方：頂点境界を差し引いた後に相殺すべき項を正確に指定する。 -/
lemma rawListDifferential_partition (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A (d := d) out =
      (∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
      else 0) +
      ∑ k ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))ᶜ,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) out k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential_eq_sum A out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h),
    ← Finset.sum_add_sum_compl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h)),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_singletonPositions A w r out h]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
