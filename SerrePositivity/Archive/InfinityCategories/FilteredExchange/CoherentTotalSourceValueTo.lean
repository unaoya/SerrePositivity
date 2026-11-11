module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeValuePre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueTo

/-!
概要：元の余極限始域の値射を、同じ指定頂点等式による固定値射として厳密に表示する。
方針：一般の頂点等式を消去し、同じ fiber の値射を回収する。
規約：値射を選び直さない。使われ方：raw 輸送から元の Kan 頂点射への指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定頂点等式による固定値射は、同じ fiber の等式射と元の値射の合成。 -/
lemma pointedFiberValueTo_eq_cast {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    pointedFiberValueTo hz =
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) hz) ≫
        (pointedSpaceFiberValueEquivalence z').hom := by
  cases hz
  simp only [pointedFiberValueTo, eqToHom_refl, Category.id_comp]

/-- 元の余錐 fiber の指定値への射は、同じ fiber 写像と固定値射の合成。 -/
lemma coconeFiberValueMapAt_eq_valueTo {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌} (hz : c.vertex = z) :
    coconeFiberValueMapAt c z hz = coconeFiberMap c ≫ pointedFiberValueTo hz := by
  rw [pointedFiberValueTo_eq_cast]
  rfl

/-- 元の余極限始域の値射は、同じ元の頂点等式で定めた固定値射そのもの。 -/
lemma coherentTotalSourceValueMap_eq_valueTo {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    coherentTotalSourceValueMap F = pointedFiberValueTo (coherentDiagramTotalCocone_vertex F) :=
  (pointedFiberValueTo_eq_cast (coherentDiagramTotalCocone_vertex F)).symm

end SerrePositivity.InfinityCategories.F2
