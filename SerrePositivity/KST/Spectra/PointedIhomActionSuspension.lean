module

public import SerrePositivity.KST.Spectra.PointedIhomActionComposition
public import SerrePositivity.KST.Spectra.SuspensionComposition

/-!
概要：内部 Hom のパラメータ作用と懸垂を厳密に交換する。
方針：豊穣合成の curry 表示と懸垂の合成保存則を使う。
規約：全 Hom の射の等式。使われ方：単位三角形の第二辺の実区間との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma parameterAction_map {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] {T P Q R P' Q' R' : C}
    (e : T ⟶ P) (p : P ⟶ P') (q : Q ⟶ Q') (r : R ⟶ R')
    (c : P ⊗ Q ⟶ R) (c' : P' ⊗ Q' ⟶ R')
    (hc : c ≫ r = (p ⊗ₘ q) ≫ c') :
    q ≫ curry ((e ≫ p) ▷ Q' ≫ c') =
      curry (e ▷ Q ≫ c) ≫ (ihom T).map r := by
  rw [← curry_natural_left, ← curry_natural_right]
  congr 1
  simp only [comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, ← tensorHom_def'_assoc, ← hc]

private lemma closedAction_post {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (A E : C) {V W : C} (f : V ⟶ W) :
    (ihom E).map f ≫ ((MonoidalClosed.pre ((ihom.ev A).app E)).app W ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A ((ihom A).obj E) W).hom) =
    ((MonoidalClosed.pre ((ihom.ev A).app E)).app V ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A ((ihom A).obj E) V).hom) ≫
      (ihom ((ihom A).obj E)).map ((ihom A).map f) := by
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post A ((ihom A).obj E) f,
    ← Category.assoc]
  simpa only [Category.assoc, Functor.id_obj, Functor.comp_obj, tensorLeft,
    curriedTensor_obj_obj] using
    congrArg (fun k => k ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A ((ihom A).obj E) W).hom)
      ((MonoidalClosed.pre ((ihom.ev A).app E)).naturality f)

/-- 内部 Hom の作用は標的への後合成について自然。 -/
lemma ihomAction_post (A E : PointedSimplicialSet.{u})
    {V W : PointedSimplicialSet.{u}} (f : V ⟶ W) :
    (ihom E).map f ≫ ihomAction A E W =
      ihomAction A E V ≫
        (ihom (PointedObject.basedHom A E)).map ((ihom A).map f) := by
  rw [ihomAction, ihomAction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (ihom E).map f ≫ ((MonoidalClosed.pre ((ihom.ev A).app E)).app W ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A ((ihom A).obj E) W).hom) =
    ((MonoidalClosed.pre ((ihom.ev A).app E)).app V ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A ((ihom A).obj E) V).hom) ≫
      (ihom ((ihom A).obj E)).map ((ihom A).map f)
  exact closedAction_post A E f

/-- パラメータ評価後も、標的への後合成の自然性を全体で保つ。 -/
lemma ihomParameterAction_post {A E V W T : PointedSimplicialSet.{u}}
    (e : T ⟶ PointedObject.basedHom A E) (f : V ⟶ W) :
    (ihom E).map f ≫ (ihomAction A E W ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A W)) =
    (ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V)) ≫
      (ihom T).map ((ihom A).map f) := by
  have hn := (MonoidalClosed.pre e).naturality ((ihom A).map f)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  rw [← Category.assoc, ihomAction_post, Category.assoc]
  erw [hn]
  exact (Category.assoc _ _ _).symm

/-- 懸垂をパラメータ作用の前後で施しても、同じ全 Hom の射を得る。 -/
lemma ihomParameterAction_suspension {A E V T : PointedSimplicialSet.{u}}
    (e : T ⟶ PointedObject.basedHom A E) :
    suspensionHom E V ≫ (ihomAction (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (e ≫ suspensionHom A E)
        (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V))) =
    (ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V)) ≫
      (ihom T).map (suspensionHom A V) := by
  rw [ihomParameterAction_eq_curry, ihomParameterAction_eq_curry]
  exact parameterAction_map e (suspensionHom A E) (suspensionHom E V)
    (suspensionHom A V) (MonoidalClosed.comp A E V)
    (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V))
    (suspensionHom_comp A E V)

end SerrePositivity.KST.Spectra.PointedMapping
