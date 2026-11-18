module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorSwapVectors

/-!
模型。文献の定義との比較は後で
# 区間の面テンソルの任意位置の隣接交換

概要：Berger–Fresse §2.2.4 の Koszul 交換を実際の反復区間の全隣接位置で評価する。
方針：先頭交換を基底とし、尾の交換を左 tensor で持ち上げる。
規約：右括弧のテンソルと既存の adjacentIso を使う。
使われ方：切断の符号変化を実際の出力置換へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open _root_.SerrePositivity.Coxeter

/-- 概要：尾の置換は先頭を保って面の族へ作用する（BF §2.2.6）。
方針：有限添字を先頭と後続へ分ける。
規約：出力への作用は添字写像との前合成。
使われ方：隣接交換の尾の再帰式。 -/
lemma cons_comp_shiftPerm (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (σ : Equiv.Perm (Fin n)) :
    Fin.cons a f ∘ shiftPerm σ = Fin.cons a (f ∘ σ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, shiftPerm_zero, Fin.cons_zero]
  · simp only [Function.comp_apply, shiftPerm_succ, Fin.cons_succ]

variable (A : Type u) [CommRing A]

/-- 概要：実際の区間面テンソルの隣接交換の Koszul 公式（BF §2.2.4）。
方針：先頭二因子の公式と尾の交換の帰納法を使う。
規約：指定した整数全次数を保ち、交換される二面の次数だけが符号を決める。
使われ方：余演算の隣接互換に対する等変性の出力側。 -/
lemma adjacentIso_tensorVectorAt (n : ℕ) (i : Fin n) (f : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (r : ℤ) (hf : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ) = r) :
    (adjacentIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n i).hom.f r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (n + 1) f r hf) =
      ((-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f i.castSucc) : ℤ)) *
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f i.succ) : ℤ))).negOnePow •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (n + 1) (f ∘ adjacentTransposition i) r
            (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_permutation]; exact hf) := by
  induction n generalizing r with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a, f, rfl⟩ := Fin.exists_cons f
    revert i
    refine Fin.cases ?_ (fun j => ?_)
    · obtain ⟨b, f, rfl⟩ := Fin.exists_cons f
      have hsum : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree a : ℤ) + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree b : ℤ) +
          -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ)) = r := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_cons] at hf
        omega
      simpa only [adjacentIso, Fin.cases_zero, adjacentTransposition,
        Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_succ,
        Matrix.cons_cons_comp_swap_zero_one] using!
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.swapFirstIso_tensorVectorAt A n a b f r hsum
    · have hsum : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree a : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ) = r := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_cons] at hf
        omega
      have hg := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_permutation (n + 1) f (adjacentTransposition j)
      simp only [← shiftPerm_adjacent, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cons_comp_shiftPerm]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_cons A (n + 1) a f r hsum,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_succ A (n + 1) (Fin.cons a (f ∘ adjacentTransposition j))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree a : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ)) r rfl
          (by change -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (f ∘ adjacentTransposition j) : ℤ) = _; rw [hg])
          hsum]
      change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ◁ (adjacentIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n j).hom).f r
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (n + 1))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree a : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ)) r hsum
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A a ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A (n + 1) f)) = _
      rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply]
      have ht := ih j f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ)) rfl
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] at ht
      rw [ht]
      simp only [Units.smul_def]
      rw [TensorProduct.tmul_smul, map_zsmul]
      rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
