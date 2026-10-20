module

public import SerrePositivity.KST.Spectra.PointedParametricPostExchange

/-!
概要：前合成の豊穣作用を、同じ内部 Hom の合成の転置として厳密表示する。
方針：全族後合成の恒等パラメータを用い、同じ転置を二度戻す。
規約：Kan 性や充填選択を使わない。使われ方：cotensor と前合成の全パラメータ交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 元の前合成作用は、同じ内部 Hom の標的作用を転置した射そのもの。 -/
lemma preAction_eq_transpose_ihomAction (W D Z : PointedSimplicialSet.{u}) :
    preAction W D Z = transpose (ihomAction W D Z) := by
  have h := parametricPost_exchange W (𝟙 (PointedObject.basedHom D Z))
  simpa only [parametricPost, Category.id_comp, preAction] using h.symm

/-- 同じ前合成作用を転置すると、元の内部 Hom の標的作用へ厳密に戻る。 -/
lemma transpose_preAction (W D Z : PointedSimplicialSet.{u}) :
    transpose (preAction W D Z) = ihomAction W D Z := by
  rw [preAction_eq_transpose_ihomAction, transpose_transpose]

/-- 元の前合成作用は、同じ豊穣合成の curry の転置。 -/
lemma preAction_eq_transpose_curry_comp (W D Z : PointedSimplicialSet.{u}) :
    preAction W D Z = transpose (curry (MonoidalClosed.comp W D Z)) := by
  rw [preAction_eq_transpose_ihomAction, ihomAction_eq_curry_comp]

end SerrePositivity.KST.Spectra.PointedMapping
