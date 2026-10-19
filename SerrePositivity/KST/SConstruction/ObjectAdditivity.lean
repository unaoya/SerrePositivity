module
public import SerrePositivity.KST.SConstruction.SimplicialProductQuillenA
public import SerrePositivity.KST.SConstruction.McCarthyFiberEquivalence

/-! # McCarthy の object S• 加法性
概要：cofiber 図式の subobject と quotient は object S• の後で積への弱同値を与える。
方針：二ホモトピーによる左 fiber の比較を単体積版 Quillen A に適用する。
規約：cofiber 図式の ∞ 圏そのものと積の同値は主張しない。使われ方：core S• 実現の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- cofiber 図式の object S• から subobject と quotient の object S• の積への射。 -/
def objectSAdditivityMap (X : StableModel.{u}) :
    objectSConstruction (cofiberStableModel X).carrier ⟶
      objectSConstruction X.carrier ⊗ objectSConstruction X.carrier :=
  CartesianMonoidalCategory.lift
    (objectSConstructionFunctor.map (cofiberStableSubobject X))
    (objectSConstructionFunctor.map (cofiberStableQuotient X))

/-- object S• の加法性：subobject・quotient の元の射対は anodyne 局所化で同型。 -/
lemma objectSAdditivityMap_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSAdditivityMap X)) :=
  simplicialProductQuillenA
    (objectSConstructionFunctor.map (cofiberStableSubobject X))
    (objectSConstructionFunctor.map (cofiberStableQuotient X))
    (fun _ a => cofiberLeftFiberQuotient_localized_isIso X a)

end SerrePositivity.KST.SConstruction
