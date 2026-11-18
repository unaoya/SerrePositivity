module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CoInsertionFaceEvaluation

/-!
模型。文献の定義との比較は後で
# 内側面テンソルの有限和へのブロック余代入

概要：Berger–Fresse §2.2.6・§3.1 の内側余演算の全有限和を前後ブロックと連結する。
方針：純粋ブロック評価を内側の有限和へ分配し、各面テンソルを実際の appendIso で連結する。
規約：添字型は任意の有限型、整数係数と交換符号を保持する。
使われ方：実際の辺・頂点余演算の有限切断和を余代入へ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：内側の符号付き面テンソル和は同じ係数の連結族の和へ移る（BF §3.1）。
方針：テンソル積と構成する複体射の加法性で分配し、各項を連結する。
規約：空和も含み、交換符号は和全体に掛ける。
使われ方：実際の内側辺余演算の非零切断和の評価。 -/
lemma coInsertionBlocks_face_sum_apply {ι : Type v} [Fintype ι] (C : Complex A) (s n t : ℕ)
    (θ : C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n)
    (c q z : ℤ) (f : Fin s → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (g : ι → Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (h : Fin t → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (hz : c + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) = z)
    (a : C.X c) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X q) (hg : ∀ j, -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (g j) : ℤ) = c + q)
    (r : ι → ℤ) (hθ : θ.f (c + q) (ιTensorObj C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) c q (c + q) rfl (a ⊗ₜ[A] y)) =
      ∑ j, r j • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (g j) (c + q) (hg j)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) C s n t θ).f z
      (ιTensorObj C (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) s ⊗ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ⊗ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t))
        c (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) s) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ⊗ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) rfl
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A s f ⊗ₜ[A] ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t)
            q (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ)) rfl
            (y ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A t h)))) =
      (c * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)).negOnePow •
        ∑ j, r j • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (s + (n + t)) (Fin.append f (Fin.append (g j) h)) z
          (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append]; have := hg j; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks_apply, hθ]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.appendIso_tensorVectorAt A n t (g j) h (c + q) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))
    (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) (hg j) rfl (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] at hi
  rw [hi]
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.appendIso_tensorVectorAt A s (n + t) f (Fin.append (g j) h)
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)) (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) z rfl
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append]; have := hg j; omega) (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] at ho
  rw [ho]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
