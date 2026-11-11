module

public import SerrePositivity.KST.Spectra.PointedBasedPathClosed

/-!
概要：内部 Hom の標的への作用を、区間と二単体の全体に使える一つの点つき射で表示する。
方針：評価への前合成と反復 curry の同じ同型を合成する。
規約：区間を選び直さない。使われ方：トレース付き単位の実構造三角形の全 Hom への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 内部 Hom の関手作用を、元の点つき写像空間の一つの射として表す。 -/
def ihomAction (A E V : PointedSimplicialSet.{u}) :
    PointedObject.basedHom E V ⟶
      PointedObject.basedHom (PointedObject.basedHom A E) (PointedObject.basedHom A V) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((ihom.ev A).app E) V ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A (PointedObject.basedHom A E) V).hom

/-- 元の実区間への内部 Hom の作用は、同じ ihomAction 射への後合成そのもの。 -/
lemma VerticalPath.basedIhomMap_path (A : PointedSimplicialSet.{u})
    {E V : PointedSimplicialSet.{u}} {f g : E ⟶ V}
    (H : VerticalPath (PointedObject.toPoint V) f g) :
    (H.basedIhomMap A).path = H.path ≫ (ihomAction A E V).right := by
  change (H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((ihom.ev A).app E) V).right) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A (PointedObject.basedHom A E) V).hom.right = _
  exact Category.assoc _ _ _

/-- 同じ実区間へ作用してからパラメータで評価しても、同じ二つの射への後合成。 -/
lemma VerticalPath.basedIhomMap_pre_path (A : PointedSimplicialSet.{u})
    {E V T : PointedSimplicialSet.{u}} {f g : E ⟶ V}
    (H : VerticalPath (PointedObject.toPoint V) f g)
    (e : T ⟶ PointedObject.basedHom A E) :
    ((H.basedIhomMap A).pre e).path =
      H.path ≫ (ihomAction A E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V)).right := by
  change (H.basedIhomMap A).path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom A V)).right = _
  rw [basedIhomMap_path, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.PointedMapping
