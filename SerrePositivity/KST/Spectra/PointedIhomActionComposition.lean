module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalAction

/-!
概要：内部 Hom の作用を豊穣合成の curry で表示する。
方針：二度 uncurry して評価の合成へ戻す。
規約：全単体次数の点つき射の等式。使われ方：単位の実構造辺と懸垂の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma closedAction_eq_curry_comp {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] (A E V : C) :
    (MonoidalClosed.pre ((ihom.ev A).app E)).app V ≫
      (ihomCurryIso A ((ihom A).obj E) V).hom = curry (MonoidalClosed.comp A E V) := by
  apply uncurry_injective
  apply uncurry_injective
  change uncurry (uncurry ((MonoidalClosed.pre ((ihom.ev A).app E)).app V ≫
    ihomCurry A ((ihom A).obj E) V)) = _
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_uncurry_ihomCurry]
  erw [associator_inv_naturality_right_assoc, id_tensor_pre_app_comp_ev,
    uncurry_curry, comp_eq, uncurry_curry, compTranspose_eq]
  rfl

/-- 内部 Hom の標的への作用は豊穣合成を curry した射そのもの。 -/
lemma ihomAction_eq_curry_comp (A E V : PointedSimplicialSet.{u}) :
    ihomAction A E V = curry (MonoidalClosed.comp A E V) := by
  rw [ihomAction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso]
  exact closedAction_eq_curry_comp A E V

/-- パラメータ評価と内部 Hom の作用を一つの豊穣合成として表示する。 -/
lemma ihomParameterAction_eq_curry {A E V T : PointedSimplicialSet.{u}}
    (e : T ⟶ PointedObject.basedHom A E) :
    ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V) =
      curry (e ▷ PointedObject.basedHom E V ≫ MonoidalClosed.comp A E V) := by
  rw [ihomAction_eq_curry_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact curry_pre_app e (MonoidalClosed.comp A E V)

end SerrePositivity.KST.Spectra.PointedMapping
