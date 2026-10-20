module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricSecondNaturality
public import SerrePositivity.KST.Spectra.SignedAdjointConstantCoordinates

/-!
概要：元の左端点の全族後合成と内部 Hom 像を、同じ交換・反転・射影の頂点へ照合する。
方針：標準族作用の三つの厳密可換式と内部 Hom の合成保存を使う。
規約：区間選択不要。使われ方：第三の定数辺と実入力境界の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 同じ左端点への全族後合成は、移した入力と同じ標的の作用の合成。 -/
lemma left_parametric_post {P A Y Z Z' : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (v : P ⟶ PointedObject.basedHom Z Z') :
    left f g ≫ targetParametricPost v = (input f g ≫ doubleParametricPost v) ≫
      PointedObject.basedHomMap P ((swap Z' ≫ reversal Z') ≫ projection Z') := by
  have hm : PointedObject.basedHomMap P ((swap Z' ≫ reversal Z') ≫ projection Z') =
      (PointedObject.basedHomMap P (swap Z') ≫ PointedObject.basedHomMap P (reversal Z')) ≫
        PointedObject.basedHomMap P (projection Z') := by
    change (ihom P).map ((swap Z' ≫ reversal Z') ≫ projection Z') = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl
  rw [left_eq, hm]
  simp only [Category.assoc]
  rw [projection_parametric, ← Category.assoc (reversal Z) (doubleParametricPost v),
    reversal_doubleParametricPost, Category.assoc,
    ← Category.assoc (swap Z) (doubleParametricPost v), swap_doubleParametricPost]
  simp only [Category.assoc]

/-- 内部 Hom に移した同じ左端点への入力も、同じ合成入力と作用へ戻る。 -/
lemma left_parametric_pre {P A A' Y Z : PointedSimplicialSet.{u}}
    (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (j : A ⟶ PointedObject.basedHom P A') :
    j ≫ PointedObject.basedHomMap P (left f g) =
      (j ≫ PointedObject.basedHomMap P (input f g)) ≫
        PointedObject.basedHomMap P ((swap Z ≫ reversal Z) ≫ projection Z) := by
  have he : left f g = input f g ≫ ((swap Z ≫ reversal Z) ≫ projection Z) := by
    rw [left_eq, Category.assoc]
  have hm : PointedObject.basedHomMap P (left f g) =
      PointedObject.basedHomMap P (input f g) ≫
        PointedObject.basedHomMap P ((swap Z ≫ reversal Z) ≫ projection Z) := by
    rw [he]
    exact CategoryTheory.Functor.map_comp (ihom P) _ _
  rw [hm]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.Spectra.SignedAdjointPaths
