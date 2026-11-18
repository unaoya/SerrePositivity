module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BoundaryRemainder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DifferentialCriterion

/-!
模型。文献の定義との比較は後で
# TR の微分と頂点境界の差の具体的な有限和

概要：Berger–Fresse §1.4.4 の残りの相殺対象を微分保存の両辺の差と同定する。
方針：一文字行の二重和を交換し、Schedule の全単射で頂点境界へ移す。
規約：残余和の零性はまだ要求される結論であり仮定しない。
使われ方：一般の Schedule の移動による相殺を閉じるべき場所を指定する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：零の分岐を持つ依存有限和は条件を満たす部分型の和（BF §1.4.4）。
方針：添字を条件とその否定に分け、各分岐を評価する。
規約：値は可換加法モノイドでよい。
使われ方：一文字行の削除の証明項を保って Schedule の和を付け替える。 -/
lemma sum_dite_zero_eq_subtype {I M : Type*} [Fintype I] [AddCommMonoid M]
    (p : I → Prop) [DecidablePred p] (f : (i : I) → p i → M) :
    (∑ i, if h : p i then f i h else 0) = ∑ i : {i // p i}, f i.val i.property := by
  have ht : (∑ i : {i // p i}, if h : p i.val then f i.val h else 0) =
      ∑ i : {i // p i}, f i.val i.property := by
    apply Finset.sum_congr rfl
    intro i _
    rw [dite_eq_left i.property]
  have hf : (∑ i : {i // ¬p i}, if h : p i.val then f i.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [dite_eq_right i.property]
  rw [← Fintype.sum_subtype_add_sum_subtype p, ht, hf, add_zero]

/-- 概要：全 Schedule の一文字行の寄与は頂点境界（BF §1.4.4）。
方針：行番号と Schedule の二重和を交換して全単射を適用する。
規約：arity は正、最終行と失敗する table も含む。
使われ方：削除和の一文字行部分を全て頂点境界へ移す。 -/
lemma sum_singleton_terms_vertexBoundary (A : Type u) [CommRing A] {n d : ℕ}
    (hn : 0 < n) (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), ∑ i : Fin (d + 2), if hi : (r.val i).val = 1 then
      (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)
    else 0) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin (d + 2), ∑ r : {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1) // (r.val i).val = 1},
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r.val i r.property) := by
      apply Finset.sum_congr rfl
      intro i _
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_dite_zero_eq_subtype _ _
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_singletonSchedules_vertexBoundary A hn w

/-- 概要：TR の微分は頂点境界に実際の残余和を加えたもの（BF §1.4.4）。
方針：削除位置の分割と一文字行の和の同定を合わせる。
規約：残余は成功 table の補集合の削除項であり、零性を仮定しない。
使われ方：残りの項の相殺を示すと一般の微分保存が従う。 -/
lemma differential_onSequence_vertexBoundary_add_remainder (A : Type u) [CommRing A]
    {n d : ℕ} (hn : 0 < n) (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w + ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_onSequence_partition A hn w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_singleton_terms_vertexBoundary A hn w]

/-- 概要：一般の頂点境界恒等式と実際の残余和の零性は同値（BF §1.4.4）。
方針：微分の分割式から既知の頂点境界を加法群で消す。
規約：零性そのものはこの判定では証明しない。
使われ方：Schedule の相殺で解くべき正確な残りの命題を与える。 -/
lemma vertexBoundary_identity_iff_remainder_zero (A : Type u) [CommRing A]
    {n d : ℕ} (hn : 0 < n) (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w ↔
      (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.differential_onSequence_vertexBoundary_add_remainder A hn w]
  constructor
  · intro h
    have hh := congrArg (fun x => -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w + x) h
    simpa only [← add_assoc, neg_add_cancel, zero_add] using hh
  · intro h
    rw [h, add_zero]

/-- 概要：実際の正規化 TR の微分保存と残余和の零性は同値（BF §1.4.4）。
方針：全生成元での判定と、微分と頂点境界の差の公式を合成する。
規約：残余和の消滅を仮定しただけの結果を微分保存の完成とは数えない。
使われ方：一般の相殺の証明を元の BE 複体上の線形写像へ戻す。 -/
lemma normalizedMap_comm_iff_remainder_zero (A : Type u) [CommRing A]
    (n d : ℕ) (hn : 0 < n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1)) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d).comp ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d).hom ↔
      ∀ w : Fin (d + 2) → Equiv.Perm (Fin n),
        (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm_iff_vertexBoundary]
  constructor
  · intro h w
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary_identity_iff_remainder_zero A hn w).mp (h w)
  · intro h w
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary_identity_iff_remainder_zero A hn w).mpr (h w)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
