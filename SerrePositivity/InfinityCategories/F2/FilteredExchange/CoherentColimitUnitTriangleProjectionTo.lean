module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeUnitValuePost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleTotalComponentMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerVertexMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleTotalAction

/-!
概要：元の五因子の上側三角形項を、同じ固定値で元の全空間作用の三角形へ照合する。
方針：元の単位の全射影式と元の三角形成分の値を同じ順で回収する。
規約：全三角形・元の指定値を保持。使われ方：同じホモトピー圏での二因子の合成。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "uJ" => coconeTransformationHomotopy (coherentDiagramTotalCocone J)
local notation "e" => FunctorIso.app (functorTriangleSequentialPostComparison T p) x₀
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)

/-- 元の上側三角形項の固定値への射影は、同じ全空間三角形の単位作用後の指定値。 -/
lemma coherentColimitUnitTriangle_projectionTo_heq_native :
    HEq (VertexIso.map (VertexIso.map e (functorHomotopyRelativePost uJ p)) Q)
      ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J)) := by
  let i := vertexFiberι ((ihom (leftUnstraightening F)).map (leftUnstraighteningProjection J))
    (functorVertex p)
  let v := (ihom (leftUnstraightening F)).map (coherentNativeUnitValueAction J)
  refine (heq_of_eq (vertexIso_map_comp e (functorHomotopyRelativePost uJ p) Q)).trans ?_
  refine (vertexIso_map_heq e (coherentNativeUnitValue_post J p)).trans ?_
  refine (functorTriangleSequentialPostComparison_total_app_map_heq T (i ≫ v)).trans ?_
  exact (heq_of_eq (vertexIso_map_comp (functorTriangleRelativeComparison T) i v).symm).trans
    (functorIso_postcomp_vertexMap_heq (functorTriangleTotalActionIso T)
      (coherentNativeUnitValueAction J)).symm

end SerrePositivity.InfinityCategories.F2
