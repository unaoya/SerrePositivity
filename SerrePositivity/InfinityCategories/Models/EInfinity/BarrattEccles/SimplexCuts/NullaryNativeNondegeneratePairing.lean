module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeZeroValues

/-!
模型。文献の定義との比較は後で
# 元の全分割を保持する非退化空語の対合

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §374。
元の分割の一意性と同じ一点Cut挿入を合成し、零項も全て残す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 元の空語分割の一意性による同じCutへの同値（BF §1.2.4）。 -/
def nullaryOverlapCutEquiv {c N q : ℕ} (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition c 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition c 0 × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut N q) ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut N q where
  toFun := Prod.snd
  invFun t := (ρ, t)
  left_inv a := by
    apply Prod.ext
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty ρ).trans
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty a.1).symm
    · rfl
  right_inv _ := rfl

/-- 同じ非退化raw語の元の全分割の項は小Cut項（BF §2.2.6）。 -/
lemma nullaryNativeCompositeTerm_eq_small
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ)
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0 × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + d) q)
    (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm A S u ν k q c x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) x (-((d + q : ℕ) : ℤ)) (by omega) c.2 := by
  have hc : c.1 = ρ :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty c.1).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_single_of_count_one ρ.count_eq_one_of_empty ρ).symm
  rcases c with ⟨ρ', t⟩
  dsimp only at hc
  subst ρ'
  have hnd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ) := by
    rw [← hw]
    exact w.property.2
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm
  rw [dite_eq_left hnd]
  have he : (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_surjective u ν k ρ, hnd⟩ :
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) = w := Subtype.ext hw.symm
  dsimp only
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign_inner_degree_zero, one_smul]

/-- 元の全分割・全Cut上で非退化空語の固定零項と相殺を与える（BF §2.2.6）。 -/
lemma nullaryNativeBalance_pairing_of_nondegenerate {m d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ) :
    ∃ τ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q (τ i) x =
          -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x) := by
  have hV : (m + 2) + d = (m + d) + 2 := by omega
  obtain ⟨p, hp, hu⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.unique_position_of_occurrenceCount_one u.val k ρ.count_eq_one_of_empty
  let P : Fin ((m + d) + 2) := Fin.cast hV p
  have hvp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val P = k ∧
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val j = k → j = P := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_unique hV u p k hp hu
  have hvw : ∀ i, k.succAbove ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val i) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val (P.succAbove i) := by
    intro i
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryRawWord_eq_mp_erase_value (by omega) u ν k ρ w hw p hu i
  let Z : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut ((m + d) + 1) q → Prop := fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u) k = 0
  let e := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOverlapCutEquiv ρ).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOutputCutEquiv (m + d) q (m + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u) P k hvp.1 hvp.2)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetPerm Z e, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetExchange_involutive Z e, ?_, ?_⟩
  · intro i hi A hA S x
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetPerm_fixed_zero Z e
      (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm A S u ν k q c x)
      (fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x)
      (fun s hs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero A S _ ν k x _ (by omega) s hs) i hi
  · intro i _ A hA S x
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetPerm_term_neg Z e
      (fun c => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm A S u ν k q c x)
      (fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x)
    · intro c
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeCompositeTerm_eq_small A S u ν k ρ w hw c x]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm_eq_insert A S _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) ν P k hvp.1 hvp.2 hvw
        x _ (by omega) c.2
    · intro s hs
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero A S _ ν k x _ (by omega) s hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
