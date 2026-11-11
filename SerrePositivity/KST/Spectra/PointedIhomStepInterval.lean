module

public import SerrePositivity.KST.Spectra.PointedIhomActionSuspension
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy

/-!
概要：同じ実区間の懸垂・構造像をパラメータ評価と交換する。
方針：懸垂と標的後合成の厳密自然性を元の区間全体へ後合成する。
規約：区間を選び直さない。使われ方：単位三角形の第二辺を評価区間へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 懸垂と構造射への後合成をまとめた、パラメータ作用の全 Hom の交換則。 -/
lemma ihomParameterAction_step {A E V W T : PointedSimplicialSet.{u}}
    (e : T ⟶ PointedObject.basedHom A E) (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V ⟶ W) :
    (suspensionHom E V ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E)).map s) ≫
      (ihomAction (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E) W ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (e ≫ suspensionHom A E)
          (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) W)) =
    (ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V)) ≫
      (ihom T).map (suspensionHom A V ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map s) := by
  rw [Category.assoc, ihomParameterAction_post, ← Category.assoc,
    ihomParameterAction_suspension, Category.assoc, Functor.map_comp]

/-- 端点の表示を変えても、懸垂・構造像の元の実区間は変わらない。 -/
lemma VerticalPath.changeEndpoints_step_path {E V W : PointedSimplicialSet.{u}}
    {f g f' g' : E ⟶ V} (H : VerticalPath (PointedObject.toPoint V) f g)
    (hf : f' = f) (hg : g' = g) (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V ⟶ W) :
    ((H.changeEndpoints hf hg).suspension.forgetProjection.basedPost s).path =
      (H.suspension.forgetProjection.basedPost s).path := by
  cases hf
  cases hg
  have he : H.changeEndpoints rfl rfl = H := by cases H; rfl
  exact congrArg (fun Q => Q.suspension.forgetProjection.basedPost s |>.path) he

/-- 構造像を移した実区間は、先に評価した同じ実区間の構造像に厳密に一致する。 -/
lemma VerticalPath.basedIhomMap_step_path {A E V W T : PointedSimplicialSet.{u}}
    {f g : E ⟶ V} (H : VerticalPath (PointedObject.toPoint V) f g)
    (e : T ⟶ PointedObject.basedHom A E) (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V ⟶ W) :
    (((H.suspension.forgetProjection.basedPost s).basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).pre
      (e ≫ suspensionHom A E)).path =
    (((H.basedIhomMap A).pre e).basedPost
      (suspensionHom A V ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map s)).path := by
  rw [VerticalPath.basedIhomMap_pre_path]
  change ((H.path ≫ (suspensionHom E V).right) ≫
    ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension E)).map s).right) ≫ _ =
    ((H.basedIhomMap A).pre e).path ≫
      ((ihom T).map (suspensionHom A V ≫ (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A)).map s)).right
  rw [VerticalPath.basedIhomMap_pre_path]
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun k => H.path ≫ k.right) (ihomParameterAction_step e s)

end SerrePositivity.KST.Spectra.PointedMapping
