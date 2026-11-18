module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Components
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion
public import Mathlib.Data.Fintype.BigOperators

/-!
模型。文献の定義との比較は後で
# 任意の語の生成元に対する実際の辺成分の切断展開

概要：Berger–Fresse §2.2.6 の実際の辺成分を退化・非全射語も含む生成元上で計算する。
方針：全射性を先に判定し、退化語には非零切断が存在しないことを使う。
規約：符号は係数環のスカラーから整数倍へ直す。
使われ方：符号付き削除微分を共通の正規化削除切断和へ展開する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：証明に依存する非零項だけを部分型の全和へ移す（BF §2.2.7 の有限添字替え）。
方針：条件を満たさない零項を除き、条件付きの有限集合を部分型へ移す。
規約：値は任意の可換加法モノイド。
使われ方：非零切断と全射削除位置の証明付きの和。 -/
lemma sum_dite_eq_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ a, P a → M) :
    (∑ a, if h : P a then f a h else 0) = ∑ a : {a // P a}, f a.val a.property := by
  classical
  calc
    _ = ∑ a ∈ Finset.univ.filter P, if h : P a then f a h else 0 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hn : ¬ P a := fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp only [dite_eq_right hn]
    _ = ∑ a : {a // P a}, if h : P a.val then f a.val h else 0 :=
      Finset.sum_subtype _ (fun _ => by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [dite_eq_left a.property]

/-- 概要：実際の辺成分は非零切断部分型上の整数符号付きテンソル和（BF §2.2.6）。
方針：退化切断の零項を取り除き、整数キャストの作用を整数倍へ直す。
規約：全 arity・全語次数を扱う。
使われ方：削除微分の各基底語を非零切断の和へ展開する。 -/
lemma edgeComponentOnWord_sum_subtype {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u =
      ∑ p : {p : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p.val)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p.val p.property) := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_dite_eq_subtype]
  simp only [Int.cast_smul_eq_zsmul]

/-- 概要：任意の語の生成元の辺成分は全射なら非零切断和、非全射なら零（BF §2.2.6）。
方針：全射・非退化語では基底公式を使い、退化語では非零切断の不存在を使う。
規約：各非零切断の証明からその語の非退化基底を構成する。
使われ方：非正規化削除項も含む実際の微分展開。 -/
lemma edgeComponent_generator {n d : ℕ} (v : Fin (n + d) → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v) =
      if hs : Function.Surjective v then
        ∑ p : {p : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v p},
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign v p.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (⟨v, hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate p.property⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
              p.val)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ p.property)
      else 0 := by
  classical
  by_cases hs : Function.Surjective v
  · rw [dite_eq_left hs]
    by_cases hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v
    · let u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d := ⟨v, hs, hn⟩
      rw [show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up u) from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A u,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_basis]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_sum_subtype A u
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_nondegenerate A v hn, map_zero]
      symm
      apply Finset.sum_eq_zero
      intro p _
      exact False.elim (hn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate p.property))
  · rw [dite_eq_right hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_surjective A v hs, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
