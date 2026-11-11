module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorWords

/-!
# 二色テンソル語の指定直和

## 概要
HA 3.2.4.7 の自由代数の比較に使う、二色の語ごとのテンソルの有限直和。

## 方針
指定包含と指定射影の直交性および全和の恒等式から、極限と余極限を同時に得る。

## 規約
直和の頂点は実際の和のテンソル冪であり、同型な別の頂点に置き換えない。

## 使われ方
二色の Schur 分解と、その包含に沿った指定比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.TensorPowers
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (X Y : C) [HasBinaryBiproduct X Y]

/-- 和のテンソル冪を頂点とする、二色の語の指定双錐。 -/
def binaryTensorBicone (n : ℕ) : Bicone (binaryTensorWordObj X Y n) where
  pt := power (X ⊞ Y) n
  π := binaryTensorWordProjection X Y n
  ι := binaryTensorWordInclusion X Y n
  ι_π := by
    classical
    intro w z
    by_cases h : w = z
    · subst z
      simpa using binaryTensorWordInclusion_projection X Y n w
    · simpa [h] using binaryTensorWordInclusion_projection_ne X Y n w z h

/-- 二色の語の指定双錐は、極限と余極限である。 -/
def binaryTensorBiconeIsBilimit (n : ℕ) : (binaryTensorBicone X Y n).IsBilimit :=
  isBilimitOfTotal _ (binaryTensorWord_total X Y n)

/-- 和のテンソル冪は、指定包含に関して入力語のテンソルの余積である。 -/
def binaryTensorWordsIsColimit (n : ℕ) :
    IsColimit (binaryTensorBicone X Y n).toCocone :=
  (binaryTensorBiconeIsBilimit X Y n).isColimit

/-- 語ごとの指定包含上で等しい射は、和のテンソル冪全体でも等しい。 -/
lemma binaryTensorWords_hom_ext (n : ℕ) {Z : C} {f g : power (X ⊞ Y) n ⟶ Z}
    (h : ∀ w, binaryTensorWordInclusion X Y n w ≫ f =
      binaryTensorWordInclusion X Y n w ≫ g) : f = g := by
  apply (binaryTensorWordsIsColimit X Y n).hom_ext
  intro j
  exact h j.as

end SerrePositivity.EInfinity
