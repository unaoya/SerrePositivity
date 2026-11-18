module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CoInsertionBlocks

/-!
模型。文献の定義との比較は後で
# 前後ブロック上の余代入の純粋斉次評価

概要：Berger–Fresse §3.1 の余代入で係数を前方ブロックの右へ動かす符号を評価する。
方針：既存の parameterCross の符号と結合子の逆を純粋元で計算する。
規約：複体・整数次数・内側出力数は任意。
使われ方：実際の二段作用の Koszul 係数の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：前後ブロックの余代入の交換符号は係数次数と前方次数の積（BF §3.1）。
方針：係数の移動・指定因子への作用・二段の連結を順に評価する。
規約：内側作用の値は任意の斉次元のまま保つ。
使われ方：区間余演算へ代入して実際の右辺を面テンソル和へ展開する。 -/
lemma coInsertionBlocks_apply (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n) (c r q b z : ℤ) (hz : c + (r + (q + b)) = z)
    (a : C.X c) (x : (power K s).X r) (y : K.X q) (w : (power K t).X b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t)) c (r + (q + b)) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t) r (q + b) (r + (q + b)) rfl
          (x ⊗ₜ[A] ιTensorObj K (power K t) q b (q + b) rfl (y ⊗ₜ[A] w)))) =
      (c * r).negOnePow • (appendIso K s (n + t)).hom.f z
        (ιTensorObj (power K s) (power K (n + t)) r (c + (q + b)) z (by omega)
          (x ⊗ₜ[A] (appendIso K n t).hom.f (c + (q + b))
            (ιTensorObj (power K n) (power K t) (c + q) b (c + (q + b)) (by omega)
              (θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) ⊗ₜ[A] w)))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [parameterCross_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.associator_inv_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
