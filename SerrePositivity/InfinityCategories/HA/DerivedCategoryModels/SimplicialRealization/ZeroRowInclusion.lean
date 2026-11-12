module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 直和全複体の零行の標準脚

## 概要
横微分が零である第零行から直和全複体への鎖写像を、同じ直和包含で定める。

## 方針
全微分の二成分を分け、横微分の消滅と零行での縦微分の符号を用いる。

## 規約
複体は整数次数の余鎖複体。全次数は横次数と縦次数の和である。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。単体的実現の次数零の標準脚と射の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Preadditive
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ))

/-- 横の零行から出る微分が零なら、各直和包含は一つの鎖写像になる。 -/
def zeroRowInclusion (hK : ∀ j : ℤ, K.d 0 j = 0) :
    K.X 0 ⟶ K.total (.up ℤ) where
  f n := K.ιTotal (.up ℤ) 0 n n (by simp [ComplexShape.π])
  comm' i j hij := by
    have hd₁ : K.d₁ (.up ℤ) 0 i j = 0 := by
      rw [K.d₁_eq' (.up ℤ) (i₁' := 1) (by simp) i j, hK 1]
      simp
    have hd₂ := K.d₂_eq (.up ℤ) 0 hij j (by simp [ComplexShape.π])
    symm
    change (K.X 0).d i j ≫ K.ιTotal (.up ℤ) 0 j j _ =
      K.ιTotal (.up ℤ) 0 i i _ ≫ (K.D₁ (.up ℤ) i j + K.D₂ (.up ℤ) i j)
    rw [comp_add, K.ι_D₁, K.ι_D₂, hd₁, zero_add, hd₂]
    simp [ComplexShape.ε₂]

/-- 零行の標準包含は二重複体の射に厳密に自然である。 -/
theorem zeroRowInclusion_naturality
    {L : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ)}
    (φ : K ⟶ L) (hK : ∀ j : ℤ, K.d 0 j = 0) (hL : ∀ j : ℤ, L.d 0 j = 0) :
    zeroRowInclusion K hK ≫ HomologicalComplex₂.total.map φ (.up ℤ) =
      φ.f 0 ≫ zeroRowInclusion L hL := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact K.ιTotal_map L φ (.up ℤ) 0 n n (by simp [ComplexShape.π])

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
