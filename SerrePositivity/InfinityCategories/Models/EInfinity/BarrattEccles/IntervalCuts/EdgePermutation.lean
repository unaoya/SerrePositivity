module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.AdjacentCutSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorAdjacentSwap
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import SerrePositivity.GroupTheory.Coxeter.PermutationInduction

/-!
模型。文献の定義との比較は後で
# 辺の区間切断成分の対称群等変性

概要：Berger–Fresse §2.2.6 の実際の辺の切断成分を出力の Koszul 置換と比較する。
方針：各隣接互換で切断符号と実際のテンソル交換を一致させ、生成元による帰納法を使う。
規約：零 arity と全語次数、任意の可換係数環を扱う。
使われ方：区間余演算の複体射の equivariance フィールドの辺入力分岐。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter

variable (A : Type u) [CommRing A]

/-- 概要：一つの非零切断の出力の隣接交換は二面次数の符号を持つ（BF §2.2.4）。
方針：面テンソルの隣接交換と置換後の出力族の一致を使う。
規約：整数の符号を実際のテンソル加群に作用させる。
使われ方：切断係数を掛けた各項の比較。 -/
lemma edgeCut_tensor_adjacent {n d : ℕ} (a : Fin n) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) d)
    (p : Fin (n + 1 + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    (adjacentIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n a).hom.f (-((d + 1 : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (n + 1) (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h)) =
      (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.castSucc) *
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.succ)) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (n + 1) (d + 1)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (adjacentTransposition a) u) p)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ p
              ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_rename_iff _ _ _).mpr h)) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (adjacentTransposition a) u) p =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p ∘ adjacentTransposition a := by
    simpa only [adjacentTransposition, Equiv.symm_swap] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_rename
      (adjacentTransposition a) u p
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.adjacentIso_tensorVectorAt A n a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (-((d + 1 : ℕ) : ℤ))
    (congrArg (fun q : ℕ => -(q : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h))
  simp only [← hf, Units.smul_def, neg_mul_neg, ← Nat.cast_mul,
    Int.coe_negOnePow_natCast] at H
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_natDegree] using! H

/-- 概要：辺の全切断成分は隣接色交換に対して等変（BF §2.2.6）。
方針：有限和の各非零項で切断係数と出力の Koszul 符号を比較する。
規約：退化項は両辺で同時に零。
使われ方：全対称群への生成元帰納。 -/
lemma edgeComponentOnWord_adjacent {n d : ℕ} (a : Fin n) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) d) :
    (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (n + 1) (adjacentTransposition a)).asIso.hom.f
      (-((d + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (adjacentTransposition a) u) := by
  rw [permutationAction_adjacent]
  change (adjacentIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n a).hom.f (-((d + 1 : ℕ) : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p
  · have hp' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (adjacentTransposition a) u).val p :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_rename_iff (adjacentTransposition a) u.val p).mpr hp
    rw [dite_eq_left hp, dite_eq_left hp']
    simp only [Int.cast_smul_eq_zsmul, map_zsmul]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeCut_tensor_adjacent A a u p hp, smul_smul, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_adjacent a u p hp]
    rfl
  · have hp' : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (adjacentTransposition a) u).val p := by
      exact fun h => hp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_rename_iff _ _ _).mp h)
    rw [dite_eq_right hp, dite_eq_right hp', map_zero]

/-- 概要：実際の辺の全切断成分は任意の色置換に対して等変（BF §2.2.6）。
方針：隣接互換の帰納法で実際の置換作用の乗法則と語の後合成則を比較する。
規約：arity 零の唯一の置換も含む。
使われ方：余演算の equivariance の辺入力を全射語基底で証明する。 -/
lemma edgeComponentOnWord_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n))
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n σ).asIso.hom.f (-((d + 1 : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ u) := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename_one]
  | succ n =>
    have H : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) d,
        (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (n + 1) σ).asIso.hom.f (-((d + 1 : ℕ) : ℤ))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ u) := by
      intro τ
      apply permutation_induction_right τ
      · intro v
        simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename_one]
      · intro ρ a hρ v
        rw [permutationAction_mul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename_mul]
        change (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (n + 1) ρ).asIso.hom.f _
          ((permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (n + 1) (adjacentTransposition a)).asIso.hom.f _
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A v)) = _
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord_adjacent]
        exact hρ _
    exact H σ u

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
