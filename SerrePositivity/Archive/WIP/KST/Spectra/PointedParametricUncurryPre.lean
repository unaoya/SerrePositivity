module

public import SerrePositivity.KST.Spectra.PointedParametricUncurryAction
public import SerrePositivity.KST.Spectra.PointedUncurryComposition

/-!
概要：元の区間の全族入力制限は、同じ uncurry 座標で入力の標準懸垂へ移る。
方針：豊穣合成の厳密保存とパラメータ評価公式を二つの交換の間で比較する。
規約：区間を選び直さない。使われ方：全 Hom 自然性正方形の標的辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma compositionParameter_map {D : Type*} [Category D] [MonoidalCategory D]
    [MonoidalClosed D] {T P Q R P' Q' R' : D}
    (e : T ⟶ P) (p : P ⟶ P') (q : Q ⟶ Q') (r : R ⟶ R')
    (c : P ⊗ Q ⟶ R) (c' : P' ⊗ Q' ⟶ R')
    (hc : c ≫ r = (p ⊗ₘ q) ≫ c') :
    q ≫ curry ((e ≫ p) ▷ Q' ≫ c') =
      curry (e ▷ Q ≫ c) ≫ (ihom T).map r := by
  rw [← curry_natural_left, ← curry_natural_right]
  congr 1
  simp only [comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, ← tensorHom_def'_assoc, ← hc]

/-- 同じ入力の全族に、元の懸垂の豊穣作用を施す標準入力。 -/
def suspensionParameter {A B P : PointedSimplicialSet.{u}}
    (j : A ⟶ PointedObject.basedHom P B) :
    suspension A ⟶ PointedObject.basedHom P (suspension B) :=
  transpose (transpose j ≫ suspensionHom A B)

/-- 同じ全族入力制限と uncurry 座標は、入力の標準懸垂と厳密に可換。 -/
lemma parametricUncurryAction_pre {A B P W : PointedSimplicialSet.{u}}
    (j : A ⟶ PointedObject.basedHom P B) :
    (ihomAction P B (loopSpace W) ≫ prePointed j (PointedObject.basedHom P (loopSpace W))) ≫
        parametricUncurryAction A P W =
      uncurryAction B W ≫ (ihomAction P (suspension B) W ≫
        prePointed (suspensionParameter j) (PointedObject.basedHom P W)) := by
  have hx : ihomAction P B (loopSpace W) ≫
      prePointed j (PointedObject.basedHom P (loopSpace W)) =
    curry (transpose j ▷ PointedObject.basedHom B (loopSpace W) ≫
      MonoidalClosed.comp A B (loopSpace W)) ≫
        (InternalHomExchange.iso A P (loopSpace W)).inv :=
    (evaluationPost_exchange j).symm
  have hm : uncurryAction B W ≫
      curry ((transpose j ≫ suspensionHom A B) ▷
        PointedObject.basedHom (suspension B) W ≫
          MonoidalClosed.comp (suspension A) (suspension B) W) =
    curry (transpose j ▷ PointedObject.basedHom B (loopSpace W) ≫
      MonoidalClosed.comp A B (loopSpace W)) ≫
        PointedObject.basedHomMap P (uncurryAction A W) :=
    compositionParameter_map (transpose j) (suspensionHom A B)
      (uncurryAction B W) (uncurryAction A W) _ _ (uncurryAction_comp A B W)
  have hy := evaluationPost_exchange (V := W) (suspensionParameter j)
  change curry (transpose (transpose (transpose j ≫ suspensionHom A B)) ▷
      PointedObject.basedHom (suspension B) W ≫
        MonoidalClosed.comp (suspension A) (suspension B) W) ≫
      (InternalHomExchange.iso (suspension A) P W).inv = _ at hy
  rw [transpose_transpose] at hy
  rw [hx, parametricUncurryAction_exchange]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ (PointedObject.basedHomMap P (uncurryAction A W)), ← hm,
    Category.assoc, hy]

end SerrePositivity.KST.Spectra.PointedMapping
