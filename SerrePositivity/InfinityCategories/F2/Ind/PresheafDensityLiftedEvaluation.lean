module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityTransformation
public import SerrePositivity.InfinityCategories.F2.Ind.SmallRelativeTargetLift
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso

/-!
概要：元の大域評価との相対同型を、元の大きい unstraightening の全空間へ持ち上げる。
方針：同じ小さい相対 Hom の全族を持ち上げ、標的の縮小同型を後合成する。
規約：元の大域評価と c1 の実現射を保持する。
使われ方：底変換後の密度評価写像と元の始点固定評価の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "r" => twistedElementsReconstruction p

omit [Quasicategory C] in
/-- 小さい相対評価射を元へ戻すと、元の pointed 評価の同じ引き戻し射。 -/
lemma presheafTwistedElementsMap_lifted :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafTwistedElementsMap F) ≫
      (smallLeftUnstraighteningIso G).hom = presheafTwistedElementsLiftedMap F :=
  smallLeftUnstraighteningLift_naturality G (presheafTwistedElementsLiftedMap F)

/-- 元の大域評価との同型は、持ち上げた元の底の図式の相対 Hom 内でも保たれる。 -/
def presheafDensityLiftedEvaluationIso :
    VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ smallLeftUnstraighteningProjection H))
        ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ (presheafDensityTransformation F).map) ≫
          (smallLeftUnstraighteningIso G).hom) (by
            rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
              Category.assoc, (presheafDensityTransformation F).over]))
      (relativeFunctorVertex (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ smallLeftUnstraighteningProjection H))
        ((SSet.uliftFunctor.{u + 1, u}).map (presheafTwistedElementsMap F) ≫
          (smallLeftUnstraighteningIso G).hom) (by
            rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
              presheafTwistedElementsMap_projection,
              twistedElementsReconstruction_projection])) := by
  have he := VertexIso.map
    (uliftVertexIso.{u, u + 1} (presheafDensityTransformation F).evaluationIso)
    (smallRelativeTargetLift G (r ≫ smallLeftUnstraighteningProjection H))
  rw [smallRelativeTargetLift_vertex, smallRelativeTargetLift_vertex] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Ind
