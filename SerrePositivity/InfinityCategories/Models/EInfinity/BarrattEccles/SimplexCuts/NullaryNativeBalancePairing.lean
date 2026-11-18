module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeNondegeneratePairing
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryRawLengthValues

/-!
模型。文献の定義との比較は後で
# 元の全空語添字の正出力対合

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §375。
反復・退化の固定零項も含む、全分割と全Cutの同じ対合を包装する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 元の退化raw合成語の全分割・全Cut項は零（BF §2.2.6）。 -/
lemma nullaryNativeBalanceTerm_eq_zero_of_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (hdeg : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ))
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x = 0 := by
  cases i with
  | inl c =>
    have hc : c.1 = ρ :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty c.1).trans
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty ρ).symm
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm A S u ν k q c x = 0
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm
    simp only [hc, dite_eq_right hdeg]
  | inr s =>
    change -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x = 0
    suffices H : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x = 0 by rw [H, neg_zero]
    have hC : (m + 1) + d = (m + d) + 1 := by omega
    have hV : (m + 2) + d = (m + d) + 2 := by omega
    obtain ⟨p, hp, hu⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.unique_position_of_occurrenceCount_one u.val k ρ.count_eq_one_of_empty
    let P : Fin ((m + d) + 2) := Fin.cast hV p
    have hvp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val P = k := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_unique hV u p k hp hu).1
    let W : Fin ((m + d) + 1) → Fin (m + 1) :=
      fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ (Fin.cast hC.symm i)
    have hw : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate W := by
      intro h
      exact hdeg ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.raw_nondegenerate_cast_iff hC (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ)).mp h)
    have hvw : ∀ i, k.succAbove (W i) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val (P.succAbove i) := by
      intro i
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryRawWord_cast_erase_value hC u ν k ρ p hu i
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_raw_degenerate A S _ W P k hvp hvw hw ν x _
      (by omega) s

/-- 元の全分割・全Cut上で空語の全正出力枝の相殺を与える（BF §2.2.6）。 -/
lemma nullaryNativeBalance_pairing {m d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 2)) :
    ∃ τ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q (τ i) x =
          -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x) := by
  classical
  by_cases hcount : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1
  · let ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0 :=
      Eq.mp (congrArg (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition c 0) hcount.symm)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single 0)
    by_cases hnd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ)
    · let w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d :=
        ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_surjective u ν k ρ, hnd⟩
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalance_pairing_of_nondegenerate u ν k ρ w rfl
    · refine ⟨Equiv.refl _, fun _ => rfl, ?_, ?_⟩
      · intro i _ A hA S x
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm_eq_zero_of_degenerate A S u ν k ρ hnd i x
      · intro i hi
        exact False.elim (hi rfl)
  · refine ⟨Equiv.refl _, fun _ => rfl, ?_, ?_⟩
    · intro i _ A hA S x
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm_eq_zero_of_count_ne_one A S u ν k q hcount i x
    · intro i hi
      exact False.elim (hi rfl)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
