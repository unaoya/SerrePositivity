module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso

/-!
概要：元の native 余極限写像の値を元の小さい宇宙の実際の射として表示する。
方針：持ち上げの全忠実性で値の射を降ろし、元の指定値比較も降ろす。
規約：元の対象と値の射を保持。使われ方：元の宇宙の Kan 引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 概要：元の native 余極限写像の値の元の宇宙での射。
方針：持ち上げた実際の値の射を降ろす。
規約：両対象は元の値。使われ方：native な引き戻し比較の実際の二射影。 -/
def coherentTotalMapNativeValueDown :
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj ⟶
      (spaceInfinityObject (coherentDiagramTotalVertex G)).obj :=
  uliftMorphismDown (coherentTotalMapNativeValue F G a)

/-- 概要：降ろした native な値の射の持ち上げは元の値の射そのもの。
方針：全忠実な持ち上げの往復。規約：厳密な等式。使われ方：指定可換性の下降。 -/
lemma coherentTotalMapNativeValueDown_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalMapNativeValueDown F G a) =
      coherentTotalMapNativeValue F G a := uliftMorphismDown_lift _

/-- 概要：降ろした native な値の射は元の具体的 Kan 頂点射と指定同型を持つ。
方針：元の指定値比較を元の宇宙へ降ろす。
規約：元の二射を保持。使われ方：元の全空間 Kan 比較と native な比較との照合。 -/
def coherentTotalMapNativeValueDownIso :
    FunctorIso (coherentTotalMapNativeValueDown F G a) (coherentTotalVertexMap F G a) :=
  functorIsoDown (functorIsoOfEq (coherentTotalMapNativeValueIso F G a)
    (coherentTotalMapNativeValueDown_lift F G a).symm rfl)

end SerrePositivity.InfinityCategories.F2
