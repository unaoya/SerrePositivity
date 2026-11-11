module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantUnstraighteningValuePost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponentMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalAction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：定値標的への元の作用の後の全三角形成分を、実射の後合成の値へ戻す。
方針：同じ全空間成分の回収と相対後合成の値への厳密な射影表示を合成する。
規約：元の全三角形・指定値を保持。使われ方：単位作用の外側因子の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}} {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (u₀ : SSet.Homotopy J (SSet.const z))
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F))
    (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap J
  (SSet.const z) (coherentVertexOfHomotopy u₀))
local notation "v" => f ≫ constantUnstraighteningFiberProjection B z ≫
  QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z)

/-- 定値作用後の元の指定成分の値は、同じ全三角形の全空間比較の後合成の値。 -/
lemma functorTriangleSequentialPostComparison_map_constantPost :
    HEq (VertexIso.map (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
      (functorHomotopyRelativePost u₀ p)) Q)
      ((functorTriangleTotalActionIso T).postcomp v) := by
  refine (heq_of_eq (vertexIso_map_comp
    ((functorTriangleSequentialPostComparison T p).app x₀)
    (functorHomotopyRelativePost u₀ p) Q)).trans ?_
  refine (functorTriangleSequentialPostComparison_total_app_map_heq T
    (functorHomotopyRelativePost u₀ p ≫ Q)).trans ?_
  refine (vertexIso_map_heq (functorTriangleRelativeComparison T)
    (constantUnstraighteningRelativeIso_value_post (leftUnstraighteningProjection J) p z f
      (leftUnstraighteningMappingVertexMap J (SSet.const z)
        (coherentVertexOfHomotopy u₀)).property)).trans ?_
  rw [functorIso_postcomp_eq_mapIso]
  exact (heq_of_eq (vertexIso_map_comp (functorTriangleRelativeComparison T) _ _)).symm

end SerrePositivity.InfinityCategories.F2
