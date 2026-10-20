module

public import SerrePositivity.EInfinity.BarrattEccles.CospanReplacement

/-!
# 具体的な E 代数の引き戻しと右導来関手の値の比較

概要：Hovey §1.3 の右導来関手の値を、実際の fibration 置換の引き戻しで計算する。
方針：fibrant 置換での導来比較同型と、包含の局所化同型を合成する。
規約：任意の局所化と右導来関手に対する比較で、モデル構造の入力仮定はない。
使われ方：E2a-4 の homotopy 引き戻しの導来性と E2b の忘却後の比較。
-/

@[expose] public section

noncomputable section

universe u v w v' w'

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：具体的な homotopy 引き戻しは右導来引き戻しの値（Hovey §1.3）。
方針：fibrant 左脚での導来比較と、元の左脚への局所化同型を合成する。
規約：二つの局所化・右導来関手は任意、E モデル構造は局所的に選ぶ。
使われ方：底で計算した対象が実際の導来引き戻しであることの保証。 -/
def homotopyPullbackDerivedIso {X Y Z : (operad A).Algebra}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    {H : Type w} [Category.{v} H] {S : Type w'} [Category.{v'} S]
    (Q : (operad A).Algebra ⥤ H) (L : Over Z ⥤ S) (RF : S ⥤ H)
    (β : pullbackFunctor A g ⋙ Q ⟶ L ⋙ RF) :
    let := modelCategory A
    ∀ [Q.IsLocalization (weakEquivalences (operad A).Algebra)]
      [L.IsLocalization (weakEquivalences (Over Z))],
      RF.IsRightDerivedFunctor β (weakEquivalences (Over Z)) →
      (Q.obj (homotopyPullback A f g) ≅ RF.obj (L.obj (Over.mk f))) := by
  let := modelCategory A
  dsimp only
  intro hQ hL hRF
  have := hQ
  have := hL
  have := hRF
  have := pullbackFunctor_isRightQuillen A g
  have := replacementOver_isFibrant A f
  have := replacementInclusion_weakEquivalence A f
  have := SerrePositivity.Quillen.rightComparison_isIso Q L β (replacementOver A f)
  have := Localization.inverts L (weakEquivalences (Over Z))
    (replacementInclusion A f) (mem_weakEquivalences _)
  exact (asIso (β.app (replacementOver A f))).trans
    (RF.mapIso (asIso (L.map (replacementInclusion A f)))).symm

end SerrePositivity.EInfinity.BarrattEccles
