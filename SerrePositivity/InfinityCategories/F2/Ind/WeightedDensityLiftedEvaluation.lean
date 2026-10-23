module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.SmallRelativeTargetLift
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso

/-!
概要：元の weighted 全評価との相対同型を、元の大きい unstraightening の全空間へ移す。
方針：同じ相対 Hom の全族を持ち上げ、標的の同じ縮小同型で後合成する。
規約：元の全評価と実現射を固定。使われ方：native 評価余錐の始点固定値写像への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "r" => twistedElementsReconstruction (weightedDensityProjection F)

/-- 同じ元の全評価との相対同型は、元の大きい全空間へ持ち上げても保たれる。 -/
def weightedDensityLiftedEvaluationIso : VertexIso
    (relativeFunctorVertex (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ smallLeftUnstraighteningProjection H))
      ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ (weightedDensityTransformation F).map) ≫
        (smallLeftUnstraighteningIso G).hom) (by
          rw [Category.assoc, smallLeftUnstraighteningIso_projection,
            ← CategoryTheory.Functor.map_comp, Category.assoc,
            (weightedDensityTransformation F).over_base]))
    (relativeFunctorVertex (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ smallLeftUnstraighteningProjection H))
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedDensityTwistedJointMap F) ≫
        (smallLeftUnstraighteningIso G).hom) (by
          rw [Category.assoc, smallLeftUnstraighteningIso_projection,
            ← CategoryTheory.Functor.map_comp, weightedDensityTwistedJointMap_projection,
            twistedElementsReconstruction_projection])) := by
  have he := (uliftVertexIso.{u, u + 1} (weightedDensityTransformation F).evaluationIso).map
    (smallRelativeTargetLift G (r ≫ smallLeftUnstraighteningProjection H))
  rw [smallRelativeTargetLift_vertex, smallRelativeTargetLift_vertex] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Ind
