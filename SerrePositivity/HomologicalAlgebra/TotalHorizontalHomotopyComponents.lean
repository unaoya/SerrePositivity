module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
import all Mathlib.Algebra.Homology.TotalComplex

/-!
# 非有界二重複体の横ホモトピーの全次数成分

## 概要
整数次数の二重複体で、横次数を一つ下げる射の族を直和全複体の成分へ移す。

## 方針
各直和因子で指定した射から totalDesc を作り、次数と微分の公式を証明する。

## 規約
有界性や各対角線の有限性は要求しない。必要な直和の存在のみを型に明記する。

## 使われ方
HA 1.2.4、Weibel §1.2。実現比較の鎖ホモトピーと、双対の積全複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)}
variable [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]

/-- 横次数を一つ下げる内側の鎖写像の族が誘導する、全複体の次数 -1 の成分。 -/
def totalHorizontalComponent (H : ∀ a : ℤ, K.X a ⟶ L.X (a - 1)) (n m : ℤ) :
    (K.total (.up ℤ)).X n ⟶ (L.total (.up ℤ)).X m :=
  K.totalDesc (fun a b _ => (H a).f b ≫ L.ιTotalOrZero (.up ℤ) (a - 1) b m)

/-- 成分の定義に使った元の直和因子上の射を保持する。 -/
@[reassoc]
theorem ι_totalHorizontalComponent (H : ∀ a : ℤ, K.X a ⟶ L.X (a - 1))
    (a b n m : ℤ) (hab : a + b = n) :
    K.ιTotal (.up ℤ) a b n hab ≫ totalHorizontalComponent H n m =
      (H a).f b ≫ L.ιTotalOrZero (.up ℤ) (a - 1) b m :=
  K.ι_totalDesc _ a b hab

/-- 全次数が一つ下がらない成分は零。 -/
theorem totalHorizontalComponent_shape (H : ∀ a : ℤ, K.X a ⟶ L.X (a - 1))
    (n m : ℤ) (hnm : ¬ (ComplexShape.up ℤ).Rel m n) :
    totalHorizontalComponent H n m = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [ι_totalHorizontalComponent, comp_zero]
  rw [L.ιTotalOrZero_eq_zero (.up ℤ) (a - 1) b m, comp_zero]
  dsimp [ComplexShape.π] at hab ⊢
  simp only [ComplexShape.up_Rel] at hnm
  omega

/-- 同じ因子からの全微分は横微分と符号付き縦微分の二項である。 -/
theorem ι_totalDifferential (a b n : ℤ) (hab : a + b = n) :
    K.ιTotal (.up ℤ) a b n hab ≫ (K.total (.up ℤ)).d n (n + 1) =
      (K.d a (a + 1)).f b ≫
        K.ιTotal (.up ℤ) (a + 1) b (n + 1) (by dsimp; omega) +
      (ComplexShape.up ℤ).ε a • ((K.X a).d b (b + 1) ≫
        K.ιTotal (.up ℤ) a (b + 1) (n + 1) (by dsimp; omega)) := by
  change _ ≫ (K.D₁ (.up ℤ) n (n + 1) + K.D₂ (.up ℤ) n (n + 1)) = _
  rw [comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq (.up ℤ) (i₁' := a + 1) (by simp) b (n + 1) (by dsimp; omega),
    K.d₂_eq (.up ℤ) a (i₂' := b + 1) (by simp) (n + 1) (by dsimp; omega)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]

end SerrePositivity.HomologicalAlgebra
