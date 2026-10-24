module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantCoconeComparison
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：元の全空間のホモトピックな二射が表す native 余錐全体を比較する。
方針：同じ内部 Hom のホモトピーを持ち上げ、標準余錐比較の充満忠実性で戻す。
規約：元の図式と標的を固定。使われ方：native な積の脚の単位表現の余錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- Kan 標的への同じホモトピーの辺を、持ち上げた内部 Hom の頂点同型にする。 -/
def liftedFunctorHomotopyVertexIso {A Z : SSet.{u}} [KanComplex Z] {a b : A ⟶ Z}
    (H : SSet.Homotopy a b) :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj Z))
      (ULift.up (functorVertex a)) (ULift.up (functorVertex b)) := by
  let e := uliftTruncatedEdge.{u, u + 1} (functorEdgeOfSimplicialHomotopy H)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj Z))) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- ホモトピックな指定射の native 余錐は、同じ余錐空間内で同型。 -/
def constantCoconeHomotopyIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌)
    {a b : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj}
    (H : SSet.Homotopy a b) :
    VertexIso (X := coconeMappingSpace F z)
      (F2.coconeMappingPointAt (F2.coherentConstantCocone F z a) z
        (F2.coherentConstantCocone_vertex F z a))
      (F2.coconeMappingPointAt (F2.coherentConstantCocone F z b) z
        (F2.coherentConstantCocone_vertex F z b)) :=
  (F2.coherentCoconeTotalComparison_isQCatEquivalence F z).isFullyFaithful.preimageVertexIso
    (F2.coherentConstantCoconeComparisonIso F z a ≪≫
      liftedFunctorHomotopyVertexIso H ≪≫ (F2.coherentConstantCoconeComparisonIso F z b).symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
