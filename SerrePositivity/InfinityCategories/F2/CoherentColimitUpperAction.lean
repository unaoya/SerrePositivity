module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerAction
public import SerrePositivity.InfinityCategories.F2.CoherentColimitNativeDiagonalRepresentation
public import SerrePositivity.InfinityCategories.F2.CoherentTotalMapNativeAction

/-!
概要：元の対角の作用と a6 の指定 native 写像の作用を、同じ全空間合成で比較する。
方針：上三角形の指定表現と元の単位の自然性を合成する。
規約：元の指定辺を保持。使われ方：下三角形の輸送比較との合成と前合成の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の正方形の対角の全空間作用は、a6 の元の指定 native 写像の全作用に同型。 -/
def coherentColimitUpperActionIso : FunctorIso (coherentColimitLowerAction B H)
    (coherentTotalMapNativeAction F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) := by
  have e := CoherentConstantRepresentation.largeIso F (coherentDiagramTotalVertex G)
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
      coherentDiagramTotalUnit G) (coherentColimitNativeDiagonalRepresentation B H)
  rw [coherentColimitNativeDiagonalRepresentation_vertex] at e
  have hn : coherentLargeTotalUnit F ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentTotalVertexMap F G
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
          coherentDiagramTotalUnit G) := by
    change (_ ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentDiagramTotalUnit F)) ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, coherentTotalVertexMap_unit]
  have en := coherentTotalMapNativeActionIso F G
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))
  exact e ≪≫ (functorIsoOfEq en rfl hn).symm

end SerrePositivity.InfinityCategories.F2
