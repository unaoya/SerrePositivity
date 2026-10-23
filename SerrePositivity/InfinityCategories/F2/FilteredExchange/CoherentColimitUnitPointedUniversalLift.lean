module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedTetrahedra

/-!
概要：元の単位三単体の全 pointed 選択を、一つの全パラメータの持ち上げにする。
方針：初期値固定の延長空間の包含を展開する。
規約：選択を一頂点に固定しない。使われ方：第零面の可変 pointed 初期値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)

/-- 元の全三単体の pointed な全選択を、元の全空間と独立な全パラメータとして展開。 -/
def coherentColimitUnitPointedTetrahedronUniversalLift :
    ((Δ[3] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      coherentColimitUnitPointedTetrahedronChoice B T k ⟶ PointedSpaceInfinity.{u} :=
  relativeFunctorUncurry (relativeFunctorExtensionSpaceι pointedSpaceProjection
    ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k)
    (scaffoldFirstVertex 3 ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 3 _
      (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)))

/-- 全選択の持ち上げは、元の同じ三単体を全パラメータで被覆する。 -/
lemma coherentColimitUnitPointedTetrahedronUniversalLift_projection :
    coherentColimitUnitPointedTetrahedronUniversalLift B T k ≫ pointedSpaceProjection =
      fst (Δ[3] ⊗ leftUnstraightening F)
        (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
          (Δ[3] ◁ leftUnstraighteningProjection F) ≫
            coherentColimitUnitPointedTetrahedronDiagram B T k :=
  relativeFunctorUncurry_projection _

end SerrePositivity.InfinityCategories.F2
