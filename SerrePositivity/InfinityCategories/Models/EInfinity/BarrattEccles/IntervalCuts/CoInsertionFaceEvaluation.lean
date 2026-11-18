module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CoInsertionBlockEvaluation

/-!
模型。文献の定義との比較は後で
# 面テンソル上の余代入の符号付き評価

概要：Berger–Fresse §2.2.6・§3.1 の余代入で前方・内側・後方の面テンソルを連結する。
方針：係数と前方ブロックの交換符号を取り出し、実際の二つの appendIso を評価する。
規約：内側作用の指定した面テンソル値の整数係数を保持する。
使われ方：区間余演算の辺・頂点の各項を共通の二段出力族へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：内側作用の一つの面テンソル値を余代入すると三つの面族が連結される（BF §3.1）。
方針：純粋ブロック評価に内側の指定値を代入し、二段の実際の連結を計算する。
規約：係数次数と前方次数の積の Koszul 符号、内側の整数係数を別々に保持する。
使われ方：実際の二段余演算の非零項の値と符号を評価する。 -/
lemma coInsertionBlocks_face_apply (C : Complex A) (s n t : ℕ)
    (θ : C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n)
    (c q z : ℤ) (f : Fin s → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (g : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (h : Fin t → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (hz : c + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) = z)
    (a : C.X c) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X q) (hg : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n g : ℤ) = c + q)
    (r : ℤ) (hθ : θ.f (c + q) (ιTensorObj C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) c q (c + q) rfl (a ⊗ₜ[A] y)) =
      r • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n g (c + q) hg) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) C s n t θ).f z
      (ιTensorObj C (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) s ⊗ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ⊗ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t))
        c (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) s) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ⊗ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) rfl
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A s f ⊗ₜ[A] ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) t)
            q (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ)) rfl
            (y ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A t h)))) =
      (c * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)).negOnePow • (r •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (s + (n + t)) (Fin.append f (Fin.append g h)) z (by
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append]; omega)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks_apply, hθ]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.appendIso_tensorVectorAt A n t g h (c + q) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))
    (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) hg rfl (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] at hi
  rw [hi]
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.appendIso_tensorVectorAt A s (n + t) f (Fin.append g h)
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree s f : ℤ)) (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree t h : ℤ))) z rfl
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_append]; omega) (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] at ho
  rw [ho]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
