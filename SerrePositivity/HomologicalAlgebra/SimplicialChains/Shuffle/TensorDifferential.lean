module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorComponents

/-!
# 自然数鎖テンソルの包含上の微分

概要：Berger–Fresse §1.1.3 の shuffle の微分条件を既存の全テンソルへ接続する。
方針：全複体の二方向の微分を斉次成分の包含で計算する。
規約：自然数次数の零端点を分け、第二項に (−1)^p を付ける。
使われ方：shuffle 鎖写像の全次数での微分可換性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：正次数二入力のテンソル包含上の微分（BF §1.1.3）。
方針：二方向の全微分の包含公式を適用する。
規約：出力全次数の括弧を p+1+q に揃える。
使われ方：shuffle の正次数微分条件を全複体へ移す。 -/
lemma tensorInclusion_d_positive (K L : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    ιTensorObj K L (p + 1) (q + 1) (p + 1 + (q + 1)) rfl ≫
        (HomologicalComplex.tensorObj K L).d (p + 1 + (q + 1)) (p + 1 + q) =
      (K.d (p + 1) p ▷ L.X (q + 1)) ≫
        ιTensorObj K L p (q + 1) (p + 1 + q) (by omega) +
      (-1 : ℤ) ^ (p + 1) •
        ((K.X (p + 1) ◁ L.d (q + 1) q) ≫
          ιTensorObj K L (p + 1) q (p + 1 + q) rfl) := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat A)) (.down ℕ)
      (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
      (q + 1) (p + 1 + q) (by dsimp; omega),
    mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat A)) (.down ℕ) (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl)
      (p + 1 + q) (by rfl)]
  simp [Units.smul_def]

/-- 概要：第一の入力が零次数のテンソル包含上の微分（BF §1.1.3）。
方針：第一方向の微分は零、第二方向の符号は1と計算する。
規約：第二の入力は q+1 次。
使われ方：shuffle の零端点の微分条件。 -/
lemma tensorInclusion_d_leftZero (K L : ChainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) :
    ιTensorObj K L 0 (q + 1) (0 + (q + 1)) rfl ≫
        (HomologicalComplex.tensorObj K L).d (0 + (q + 1)) (0 + q) =
      (K.X 0 ◁ L.d (q + 1) q) ≫ ιTensorObj K L 0 q (0 + q) rfl := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
    mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat A)) (.down ℕ) 0
      (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl)
      (0 + q) rfl]
  simp

/-- 概要：第二の入力が零次数のテンソル包含上の微分（BF §1.1.3）。
方針：第二方向の微分は零と計算する。
規約：第一の入力は p+1 次。
使われ方：shuffle の零端点の微分条件。 -/
lemma tensorInclusion_d_rightZero (K L : ChainComplex (ModuleCat.{u} A) ℕ) (p : ℕ) :
    ιTensorObj K L (p + 1) 0 (p + 1 + 0) rfl ≫
        (HomologicalComplex.tensorObj K L).d (p + 1 + 0) (p + 0) =
      (K.d (p + 1) p ▷ L.X 0) ≫ ιTensorObj K L p 0 (p + 0) rfl := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat A)) (.down ℕ)
      (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
      0 (p + 0) rfl,
    mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)]
  simp

end SerrePositivity.SimplicialChains.Shuffle
