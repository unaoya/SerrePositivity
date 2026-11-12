module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
public import Mathlib.Algebra.Homology.Homotopy
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
import all Mathlib.Algebra.Homology.TotalComplex

/-!
# 実現全複体の第一行が与える指定ホモトピー

## 概要
横次数 -1 の直和包含が、横微分の後に零行の標準脚を合成した射を零に結ぶ。

## 方針
全微分の横成分と、符号が負になる縦成分を分けて相殺する。

## 規約
ホモトピーの成分も同じ直和包含。単体的複体への適用では二つの面写像を結ぶ。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。native 実現余錐の高次成分との照合の線形入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Preadditive HomologicalComplex
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ))

/-- 第一行の同じ直和包含が与える、横微分の標準脚への合成の零ホモトピー。 -/
def firstRowHomotopy (hK : ∀ j : ℤ, K.d 0 j = 0) :
    Homotopy (K.d (-1) 0 ≫ zeroRowInclusion K hK) 0 where
  hom i j := K.ιTotalOrZero (.up ℤ) (-1) i j
  zero i j hij := by
    apply K.ιTotalOrZero_eq_zero
    dsimp [ComplexShape.π]
    simp only [ComplexShape.up_Rel] at hij
    omega
  comm i := by
    have h₁ := K.d₁_eq (.up ℤ) (i₁ := -1) (i₁' := 0) (by simp) i i
      (by simp [ComplexShape.π])
    have h₂ := K.d₂_eq (.up ℤ) (-1) (i₂ := i) (i₂' := i + 1) (by simp) i
      (by simp [ComplexShape.π])
    have hd : K.ιTotalOrZero (.up ℤ) (-1) i (i - 1) ≫
        (K.total (.up ℤ)).d (i - 1) i =
        (K.d (-1) 0).f i ≫ K.ιTotal (.up ℤ) 0 i i (by simp [ComplexShape.π]) -
        (K.X (-1)).d i (i + 1) ≫
          K.ιTotalOrZero (.up ℤ) (-1) (i + 1) i := by
      rw [K.ιTotalOrZero_eq (.up ℤ) (-1) i (i - 1) (by dsimp; omega)]
      change _ ≫ (K.D₁ (.up ℤ) (i - 1) i + K.D₂ (.up ℤ) (i - 1) i) = _
      rw [comp_add, K.ι_D₁, K.ι_D₂, h₁, h₂]
      simp [ComplexShape.ε₁, ComplexShape.ε₂, sub_eq_add_neg,
        HomologicalComplex₂.ιTotalOrZero_eq, ComplexShape.π]
    rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel i (i + 1)),
      prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (i - 1) i)]
    change (K.d (-1) 0).f i ≫ (zeroRowInclusion K hK).f i =
      (K.X (-1)).d i (i + 1) ≫ K.ιTotalOrZero (.up ℤ) (-1) (i + 1) i +
        K.ιTotalOrZero (.up ℤ) (-1) i (i - 1) ≫ (K.total (.up ℤ)).d (i - 1) i + 0
    rw [hd]
    dsimp [zeroRowInclusion]
    abel

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
