module

public import SerrePositivity.KST.Spectra.PointedBasedPathDifference

/-!
概要：loop 値の同じ実区間と三角形を、元の評価で uncurry する。
方針：懸垂と評価への後合成を、一つの内部 Hom 射として保持する。
規約：区間を選び直さない。使われ方：単位の構造区間と保存した二単体の同時移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- loop 値の射を元の uncurry へ送る、同じ評価の点つき射。 -/
def uncurryAction (A V : PointedSimplicialSet.{u}) :
    PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V) ⟶ PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) V :=
  suspensionHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V) ≫
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) ((ihom.ev PointedSimplicialSet.circle.{u}).app V)

/-- loop 値の同じ実区間を、懸垂と元の評価で uncurry する。 -/
def VerticalPath.basedUncurry {A V : PointedSimplicialSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V}
    (P : VerticalPath (PointedObject.toPoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V)) f g) :
    VerticalPath (PointedObject.toPoint V) (uncurry f) (uncurry g) :=
  P.suspension.forgetProjection.basedPost ((ihom.ev PointedSimplicialSet.circle.{u}).app V)

/-- 移した区間の実辺全体は、元の同じ uncurryAction への像。 -/
lemma VerticalPath.basedUncurry_path {A V : PointedSimplicialSet.{u}}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V} (P : VerticalPath (PointedObject.toPoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V)) f g) :
    P.basedUncurry.path = P.path ≫ (uncurryAction A V).right :=
  P.suspension_basedPost_path ((ihom.ev PointedSimplicialSet.circle.{u}).app V)

end SerrePositivity.KST.Spectra.PointedMapping
