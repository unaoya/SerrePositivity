module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.F1.Universe.FunctorSpace
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport

/-!
概要：元の全空間射の指定同型を縮小した全空間射の同型へ移す。
方針：縮小同型で共役し、内部 Hom の宇宙同型と頂点同型の下降を使う。
規約：両端の実際の射を保持。使われ方：元の二三角形の可換性を小さい全空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：持ち上げた二射の指定関手同型を元の宇宙へ戻す。
方針：内部 Hom の宇宙同型と頂点同型の下降。
規約：元の二射を保持。使われ方：縮小した全空間の指定可換性。 -/
def functorIsoDown {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)) :
    FunctorIso f g :=
  downVertexIso (VertexIso.map e (uliftFunctorSpaceIso.{u, v} X Y).inv)

/-- 概要：元の大きい全空間射の指定同型を元の小さい二射へ移す。
方針：元の縮小同型の共役と内部 Hom の下降。
規約：元の全空間射を縮小した値。使われ方：coherent な錐の元の可換同型。 -/
def smallUnstraighteningFunctorIso {B : SSet.{u}} [Quasicategory B]
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {f g : leftUnstraightening F ⟶ leftUnstraightening G} (e : FunctorIso f g) :
    FunctorIso (smallLeftUnstraighteningOverMap F G f) (smallLeftUnstraighteningOverMap F G g) := by
  have h := (e.precomp (smallLeftUnstraighteningIso F).hom).postcomp
    (smallLeftUnstraighteningIso G).inv
  apply functorIsoDown.{u, u + 1}
  exact functorIsoOfEq h (smallSimplicialMap_ulift f).symm (smallSimplicialMap_ulift g).symm

end SerrePositivity.InfinityCategories.F2
